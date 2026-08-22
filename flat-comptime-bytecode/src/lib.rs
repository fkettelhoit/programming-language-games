#[derive(Debug, Clone, Copy)]
pub struct Slot {
    pub op: Op,
    pub meta: Meta,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Meta {
    pub mark: bool,
    pub shift: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Op {
    Int(i64),
    Var { elem: usize },
    Ref { offset: usize },
    Sized(SizedOp, usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SizedOp {
    BlobStart,
    BlobEnd,
    FnStart,
    FnEnd { args: usize },
    Call { args: usize, comptime: bool },
    List { elems: usize },
    Push { elems: usize },
    Set,
    Get,
    If,
    Len,
    Bin(BinOp),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinOp {
    Eq,
    Add,
    Sub,
    Mul,
}

use Op::*;
use SizedOp::*;

impl From<Op> for Slot {
    fn from(op: Op) -> Self {
        Slot { op, meta: Meta::default() }
    }
}

impl Slot {
    fn size(&self) -> usize {
        match self.op {
            Sized(BlobStart | BlobEnd | FnStart | FnEnd { .. }, slots) => slots + 2,
            Sized(_, slots) => slots + 1,
            _ => 1,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CallFrame {
    pub floor: usize,
    pub base: usize,
    pub args: usize,
    pub ret: Option<usize>,
    pub is_deferred: bool,
}

#[derive(Debug)]
pub struct Vm {
    pub ip: usize,
    pub end: usize,
    pub stack: Vec<Slot>,
    pub frames: Vec<CallFrame>,
}

const ERR_VAR_OUT_OF_BOUNDS: &str = "Variable index is out of bounds";
const ERR_INDEX_OUT_OF_BOUNDS: &str = "List index is out of bounds";
const ERR_NO_CALL_FRAME: &str = "No active call frame";
const ERR_NO_OP: &str = "No op at instruction pointer";
const ERR_INVALID_ARITY: &str = "Arity mismatch";
const ERR_INVALID_REF: &str = "Invalid ref offset";
const ERR_INVALID_FN: &str = "Invalid function";
const ERR_INVALID_LIST: &str = "Invalid list";
const ERR_INVALID_INT: &str = "Invalid int";
const ERR_INT_OVERFLOW: &str = "Int overflow";
const ERR_BLOB_END: &str = "Found unexpected blob end instruction";
const ERR_UNDERFLOW: &str = "Stack underflow";

impl Vm {
    pub fn load(code: Vec<Op>) -> Self {
        let stack: Vec<_> = code.into_iter().map(|op| Slot { op, meta: Meta::default() }).collect();
        Vm { ip: 0, end: stack.len(), stack, frames: vec![] }
    }

    fn sp(&self) -> usize {
        self.stack.len() - 1
    }

    fn op(&self, sp: usize) -> Result<Op, &'static str> {
        Ok(self.stack.get(sp).ok_or(ERR_UNDERFLOW)?.op)
    }

    fn push(&mut self, op: Op) {
        self.stack.push(op.into())
    }

    fn sum_size(&self, src: usize, n: usize) -> Result<usize, &'static str> {
        let mut sp = src;
        for _ in 0..n {
            let size = self.stack.get(sp).ok_or(ERR_UNDERFLOW)?.size();
            sp = sp.checked_sub(size).ok_or(ERR_UNDERFLOW)?;
        }
        Ok(src - sp)
    }

    fn borrow(&self, src: usize, dst: usize) -> Result<Op, &'static str> {
        Ok(match self.op(src)? {
            v @ (Int(_) | Var { .. }) => v,
            Ref { offset } if offset > src => return Err(ERR_INVALID_REF),
            Ref { offset } => Ref { offset: dst - (src - offset) },
            Sized(_, _) => Ref { offset: dst - src },
        })
    }

    fn push_borrows(&mut self, mut src: usize, n: usize) -> Result<(), &'static str> {
        let top = self.stack.len() - 1 + n;
        self.stack.resize(self.stack.len() + n, Int(0).into());
        for i in 0..n {
            let slot = self.stack[src];
            self.stack[top - i] = self.borrow(src, top - i)?.into();
            src = src.checked_sub(slot.size()).ok_or(ERR_UNDERFLOW)?;
        }
        Ok(())
    }

    fn resolve_slot(&self, sp: usize) -> Result<usize, &'static str> {
        match self.op(sp)? {
            Ref { offset } => sp.checked_sub(offset).ok_or(ERR_INVALID_REF),
            _ => Ok(sp),
        }
    }

    fn resolve_var(&self, n: usize) -> Result<usize, &'static str> {
        match self.frames.last() {
            None => return Err(ERR_NO_CALL_FRAME),
            Some(CallFrame { args, .. }) if n >= *args => return Err(ERR_VAR_OUT_OF_BOUNDS),
            Some(CallFrame { base, .. }) => Ok(base + n),
        }
    }

    fn mark(&mut self, sp: usize) -> Result<(), &'static str> {
        for sp in sp - self.stack[sp].size() + 1..=sp {
            self.stack.get_mut(sp).ok_or(ERR_UNDERFLOW)?.meta.mark = true;
        }
        Ok(())
    }

    fn compact(&mut self, floor: usize) -> Result<(), &'static str> {
        // resolve the return value first
        let ret = self.resolve_slot(self.sp())?;
        match self.op(ret)? {
            Sized(List { elems: n }, _) if self.sum_size(ret - 1, n)? == n => {
                for sp in ret - n..=ret {
                    self.stack.get_mut(sp).ok_or(ERR_UNDERFLOW)?.meta.mark = true;
                }
            }
            _ => self.mark(ret)?,
        }
        // pass 1: mark (bottom <- top)
        for sp in (floor..=ret).rev() {
            if self.stack[sp].meta.mark {
                if let Ref { offset } = self.stack[sp].op {
                    let r = sp.checked_sub(offset).ok_or(ERR_INVALID_REF)?;
                    if r >= floor && r < sp {
                        self.mark(r)?;
                    }
                }
            }
        }
        // pass 2: compact (bottom -> top)
        let mut gap = 0;
        for sp in floor..=ret {
            let mut slot = self.stack[sp];
            if slot.meta.mark {
                if let Ref { offset } = slot.op {
                    let shift = if sp - offset >= floor {
                        self.stack.get(sp - offset).ok_or(ERR_UNDERFLOW)?.meta.shift
                    } else {
                        0
                    };
                    let src = sp - gap;
                    let dst = sp - offset - shift;
                    slot.op = Ref { offset: src - dst };
                }
                self.stack[sp].meta.shift = gap;
                self.stack[sp - gap].op = slot.op;
                self.stack[sp - gap].meta.mark = false;
            } else {
                gap += 1;
            }
        }
        self.stack.truncate(ret + 1 - gap);
        if let Slot { op: Sized(_, slots), .. } = self.stack.last_mut().ok_or(ERR_UNDERFLOW)? {
            *slots = (ret - gap) - floor;
        }
        Ok(())
    }

    fn has_comptime(&self, slots: usize) -> Result<bool, &'static str> {
        let mut sp = self.ip + 1;
        while sp <= self.ip + slots {
            match self.op(sp)? {
                Sized(Call { args: _, comptime: true }, _) => return Ok(true),
                Sized(BlobStart, slots) => sp += slots + 2,
                _ => sp += 1,
            }
        }
        return Ok(false);
    }

    fn is_value(&self, sp: usize) -> Result<bool, &'static str> {
        Ok(match self.op(sp)? {
            Int(_) | Sized(BlobEnd | FnEnd { .. }, _) => true,
            Sized(List { elems }, _) if self.sum_size(sp - 1, elems)? == elems => true,
            _ => false,
        })
    }

    fn is_deferred(&self) -> bool {
        self.frames.last().map(|f| f.is_deferred).unwrap_or(true)
    }

    fn defer(&mut self, op: SizedOp, args: usize) -> Result<bool, &'static str> {
        let mut sp = self.sp();
        let mut is_unresolved = false;
        let allow_vars = matches!(op, Call { .. });
        for _ in 0..args {
            match self.op(sp)? {
                Var { .. } if allow_vars => {}
                _ if self.is_value(self.resolve_slot(sp)?)? => {}
                _ => is_unresolved = true,
            }
            let size = self.stack.get(sp).ok_or(ERR_UNDERFLOW)?.size();
            sp = sp.checked_sub(size).ok_or(ERR_UNDERFLOW)?;
        }
        if is_unresolved {
            self.push(Sized(op, self.sp() - sp));
            self.ip += 1;
        }
        Ok(is_unresolved)
    }

    fn eval_once(&mut self, comptime: bool) -> Result<(), &'static str> {
        match self.stack.get(self.ip).copied().ok_or(ERR_NO_OP)?.op {
            Int(i) => {
                self.push(Int(i));
                self.ip += 1;
            }
            Ref { offset } => {
                if offset == 0 || offset > self.ip {
                    return Err(ERR_INVALID_REF);
                }
                self.push(self.borrow(self.ip - offset, self.stack.len())?);
                self.ip += 1;
            }
            Var { elem } => {
                self.push(self.borrow(self.resolve_var(elem)?, self.stack.len())?);
                self.ip += 1;
            }
            Sized(FnStart, slots)
                if comptime && self.is_deferred() && self.has_comptime(slots)? =>
            {
                let Sized(FnEnd { args }, _) = self.op(self.ip + 1 + slots)? else {
                    return Err(ERR_INVALID_FN);
                };
                self.push(Sized(FnStart, 0 /* will be set at FnEnd */));
                let (floor, base, args) = if args == 0 {
                    match self.frames.last().copied() {
                        Some(CallFrame { base, args, .. }) => (self.stack.len(), base, args),
                        None => (self.stack.len(), self.stack.len(), 0),
                    }
                } else {
                    for n in 0..args {
                        self.push(Var { elem: n });
                    }
                    let base = self.stack.len() - args;
                    (base, base, args)
                };
                self.frames.push(CallFrame { floor, base, args, ret: None, is_deferred: true });
                self.ip += 1;
            }
            Sized(FnStart, slots) | Sized(BlobStart, slots) => {
                let offset = (self.sp() - self.ip).checked_sub(slots).ok_or(ERR_UNDERFLOW)?;
                self.push(Ref { offset });
                self.ip += slots + 2;
            }
            Sized(FnEnd { args, .. }, _) => {
                let CallFrame { floor, ret, .. } = self.frames.pop().ok_or(ERR_NO_CALL_FRAME)?;
                let sp = self.sp();
                let threatened = sp - floor;
                match self.op(sp)? {
                    v @ (Int(_) | Var { .. }) => {
                        self.stack.truncate(floor);
                        self.push(v);
                    }
                    Ref { offset } if sp - offset < floor => {
                        self.stack.truncate(floor);
                        self.push(Ref { offset: offset - threatened });
                    }
                    Sized(List { elems }, slots) if !comptime && threatened - slots <= slots => {
                        self.stack[sp].op = Sized(List { elems }, sp - floor);
                    }
                    _ => self.compact(floor)?,
                }
                match ret {
                    Some(ret) => self.ip = ret,
                    None => {
                        let slots = self.stack.len() - floor;
                        self.stack.get_mut(floor - 1).ok_or(ERR_UNDERFLOW)?.op =
                            Sized(FnStart, slots);
                        self.push(Sized(FnEnd { args }, slots));
                        self.ip += 1;
                    }
                }
            }
            Sized(BlobEnd, _) => return Err(ERR_BLOB_END),
            Sized(op @ Call { args, comptime: _ }, _)
                if comptime && self.defer(op, args + 1)? => {}
            Sized(Call { args, comptime: false }, _) if comptime && self.is_deferred() => {
                let slots_args = self.sum_size(self.sp(), args)?;
                let sp_op = self.sp() - slots_args;
                let slots = slots_args + self.stack[sp_op].size();
                self.push(Sized(Call { args, comptime: false }, slots));
                self.ip += 1;
            }
            Sized(Call { args, comptime: f_ct }, _) => {
                let sp_args = self.sp();
                let slots_args = self.sum_size(sp_args, args)?;
                let sp_op = sp_args - slots_args;
                let slots_op = self.stack[sp_op].size();
                let sp_f = self.resolve_slot(sp_op)?;
                let ret = Some(self.ip + 1);
                match self.op(sp_f)? {
                    Sized(FnEnd { args: a }, _) if args != a => return Err(ERR_INVALID_ARITY),
                    Sized(FnEnd { .. }, slots_f) => {
                        if slots_args > args {
                            self.push_borrows(sp_args, args)?;
                        }
                        self.ip = sp_f.checked_sub(slots_f).ok_or(ERR_UNDERFLOW)?;
                        self.frames.push(CallFrame {
                            floor: sp_op - slots_op + 1,
                            base: self.stack.len() - args,
                            args,
                            ret,
                            is_deferred: false,
                        });
                    }
                    Sized(List { elems }, _) if elems > 0 => {
                        let sp_code = self.resolve_slot(sp_f - elems)?;
                        match self.op(sp_code)? {
                            Sized(FnEnd { args: a }, _) if elems - 1 + args != a => {
                                return Err(ERR_INVALID_ARITY);
                            }
                            Sized(FnEnd { .. }, slots_code) => {
                                self.push_borrows(sp_f - 1, elems - 1)?;
                                self.push_borrows(sp_args, args)?;
                                self.ip = sp_code - slots_code;
                                let arity = elems - 1 + args;
                                self.frames.push(CallFrame {
                                    floor: sp_op - slots_op + 1,
                                    base: self.stack.len() - arity,
                                    args: arity,
                                    ret,
                                    is_deferred: false,
                                });
                            }
                            _ if comptime && !self.is_value(sp_code)? => {
                                self.push(Sized(
                                    Call { args, comptime: f_ct },
                                    slots_args + slots_op,
                                ));
                                self.ip += 1;
                            }
                            _ => return Err(ERR_INVALID_FN),
                        }
                    }
                    _ if comptime && !self.is_value(sp_f)? => {
                        self.push(Sized(Call { args, comptime: f_ct }, slots_args + slots_op));
                        self.ip += 1;
                    }
                    _ => return Err(ERR_INVALID_FN),
                }
            }
            Sized(op @ List { elems }, _) if comptime && self.defer(op, elems)? => {}
            Sized(List { elems }, _) => {
                let mut slots = self.sum_size(self.sp(), elems)?;
                if slots > elems {
                    self.push_borrows(self.sp(), elems)?;
                    slots += elems;
                }
                self.push(Sized(List { elems }, slots));
                self.ip += 1;
            }
            Sized(op @ Push { elems }, _) if comptime && self.defer(op, elems + 1)? => {}
            Sized(Push { elems: n }, _) => {
                let sp = self.sp();
                let slots_tail = self.sum_size(sp, n as usize)?;
                let sp_op = sp - slots_tail;
                let sp_list = self.resolve_slot(sp_op)?;
                let Sized(List { elems }, slots_old) = self.op(sp_list)? else {
                    return Err(ERR_INVALID_LIST);
                };
                self.push_borrows(sp_list - 1, elems)?;
                self.push_borrows(sp, n as usize)?;
                let base = if sp_list == sp_op { sp_list - slots_old } else { sp_op };
                self.push(Sized(List { elems: elems + n as usize }, self.stack.len() - base));
                self.ip += 1;
            }
            Sized(op @ Set, _) if comptime && self.defer(op, 3)? => {}
            Sized(Set, _) => {
                // TODO once direct mutation lands: Make sure it's impossible to create forward-refs
                let Int(i) = self.op(self.sp())? else {
                    return Err(ERR_INVALID_INT);
                };
                let sp_elem = self.sp() - 1;
                let elem_size = self.stack.get(sp_elem).ok_or(ERR_UNDERFLOW)?.size();
                let sp_op = self.sp() - 1 - elem_size;
                let sp_list = self.resolve_slot(sp_op)?;
                let Sized(List { elems }, slots_old) = self.op(sp_list)? else {
                    return Err(ERR_INVALID_LIST);
                };
                if i < 0 || i as usize >= elems {
                    return Err(ERR_INDEX_OUT_OF_BOUNDS);
                }
                self.push_borrows(sp_list - 1, elems)?;
                let sp_i = self.stack.len() - elems + i as usize;
                self.stack[sp_i] = self.borrow(sp_elem, sp_i)?.into();
                let base = if sp_list == sp_op { sp_list - slots_old } else { sp_op };
                self.push(Sized(List { elems }, self.stack.len() - base));
                self.ip += 1;
            }
            Sized(op @ Get, _) if comptime && self.defer(op, 2)? => {}
            Sized(Get, _) => {
                let [.., _, i] = self.stack.as_slice() else {
                    return Err(ERR_UNDERFLOW);
                };
                let Int(i) = i.op else {
                    return Err(ERR_INVALID_INT);
                };
                let sp_op = self.sp() - 1;
                let sp_list = self.resolve_slot(sp_op)?;
                let Sized(List { elems }, slots_list) = self.op(sp_list)? else {
                    return Err(ERR_INVALID_LIST);
                };
                if i < 0 || i as usize >= elems {
                    return Err(ERR_INDEX_OUT_OF_BOUNDS);
                };
                let sp_elem = sp_list - (elems - i as usize);
                if sp_list != sp_op {
                    self.stack[sp_op] = self.borrow(sp_elem, sp_op)?.into();
                    self.stack.truncate(sp_op + 1);
                } else {
                    let base = sp_list - slots_list;
                    match self.op(sp_elem)? {
                        Int(i) => {
                            self.stack.truncate(base);
                            self.push(Int(i));
                        }
                        Ref { offset } if sp_elem - offset < base => {
                            self.stack.truncate(base);
                            self.push(Ref { offset: base - (sp_elem - offset) });
                        }
                        Ref { offset } => {
                            let sp_ref = self.sp();
                            self.stack[sp_ref].op = Ref { offset: sp_ref - (sp_elem - offset) };
                            self.compact(base)?;
                        }
                        s @ Sized(List { elems: 0 }, 0) => {
                            self.stack.truncate(base);
                            self.push(s);
                        }
                        _ => return Err(ERR_INVALID_LIST),
                    }
                }
                self.ip += 1;
            }
            Sized(op @ If, _) if comptime && self.defer(op, 3)? => {}
            Sized(If, _) => {
                let cond = self.op(self.sp())?;
                let Int(cond) = cond else {
                    return Err(ERR_INVALID_INT);
                };
                let f = self.sp() - 1;
                let size_f = self.stack.get(f).ok_or(ERR_UNDERFLOW)?.size();
                let t = f.checked_sub(size_f).ok_or(ERR_UNDERFLOW)?;
                let sp_f = self.resolve_slot(f)?;
                let sp_t = self.resolve_slot(t)?;
                match (self.op(sp_t)?, self.op(sp_f)?) {
                    (Sized(FnEnd { args: a }, slots_t), Sized(FnEnd { args: b }, slots_f)) => {
                        if a != 0 || b != 0 {
                            return Err(ERR_INVALID_ARITY);
                        }
                        let CallFrame { base, args, is_deferred, .. } =
                            self.frames.last().copied().ok_or(ERR_NO_CALL_FRAME)?;
                        let ret = Some(self.ip + 1);
                        self.frames.push(CallFrame { floor: t, base, args, ret, is_deferred });
                        self.ip = if cond == 0 { sp_f - slots_f } else { sp_t - slots_t };
                    }
                    (_, _) => return Err(ERR_INVALID_FN),
                }
            }
            Sized(op @ Len, _) if comptime && self.defer(op, 1)? => {}
            Sized(Len, _) => {
                let sp_op = self.resolve_slot(self.sp())?;
                match self.op(sp_op)? {
                    Sized(List { elems }, _) if sp_op < self.sp() => {
                        self.stack.pop();
                        self.push(Int(elems as i64));
                    }
                    Sized(List { elems }, slots) => {
                        self.stack.truncate(self.sp().checked_sub(slots).ok_or(ERR_UNDERFLOW)?);
                        self.push(Int(elems as i64));
                    }
                    _ => return Err(ERR_INVALID_LIST),
                }
                self.ip += 1;
            }
            Sized(op @ Bin(_), _) if comptime && self.defer(op, 2)? => {}
            Sized(Bin(op), _) => {
                let [.., a, b] = self.stack.as_slice() else {
                    return Err(ERR_UNDERFLOW);
                };
                let (Int(a), Int(b)) = (a.op, b.op) else {
                    return Err(ERR_INVALID_INT);
                };
                let slot = match op {
                    BinOp::Eq if a == b => Int(1),
                    BinOp::Eq => Int(0),
                    BinOp::Add => Int(a.checked_add(b).ok_or(ERR_INT_OVERFLOW)?),
                    BinOp::Sub => Int(a.checked_sub(b).ok_or(ERR_INT_OVERFLOW)?),
                    BinOp::Mul => Int(a.checked_mul(b).ok_or(ERR_INT_OVERFLOW)?),
                };
                self.stack.truncate(self.stack.len() - 2);
                self.push(slot);
                self.ip += 1;
            }
        }
        Ok(())
    }

    pub fn run(&mut self, comptime: bool) -> Result<(), &'static str> {
        while self.ip != self.end {
            self.eval_once(comptime)?;
        }
        Ok(())
    }
}
