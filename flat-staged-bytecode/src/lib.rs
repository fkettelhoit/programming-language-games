#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Slot {
    Int(i64),
    Var { elem: usize },
    Ref { offset: usize },
    Op(SlotOp, usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SlotOp {
    // TODO: does it make sense that FuncStart and BlobStart are here? Even though their size is reversed?
    FuncStart,
    FuncEnd,
    BlobStart,
    BlobEnd,
    Call { args: usize },
    Macro { args: usize },
    List { elems: usize },
    Set { index: Option<usize> },
    Get { index: Option<usize> },
    Push { elems: Option<usize> },
    Pop { elems: Option<usize> },
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

use Slot::*;
use SlotOp::*;

impl Slot {
    fn size(&self) -> usize {
        match self {
            Op(FuncStart | FuncEnd | BlobStart | BlobEnd, slots) => slots + 2,
            Op(_, slots) => slots + 1,
            _ => 1,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CallFrame {
    pub floor: usize,
    pub base: usize,
    pub args: usize,
    pub ret: usize,
}

#[derive(Debug)]
pub struct Vm {
    pub ip: usize,
    pub end: usize,
    pub stack: Vec<Slot>,
    pub frames: Vec<CallFrame>,
}

const ERR_UNRESOLVED_VAR: &str = "Unresolved var on the output stack";
const ERR_VAR_OUT_OF_BOUNDS: &str = "Variable index is out of bounds";
const ERR_NO_CALL_FRAME: &str = "No active call frame";
const ERR_NO_OP: &str = "No op at instruction pointer";
const ERR_INVALID_REF: &str = "Invalid ref offset";
const ERR_INVALID_FUNC: &str = "Invalid function";
const ERR_INVALID_LIST: &str = "Invalid list";
const ERR_INVALID_INT: &str = "Invalid int";
const ERR_INT_OVERFLOW: &str = "Int overflow";
const ERR_BLOB_END: &str = "Found unexpected blob end instruction";
const ERR_STACK_UNDERFLOW: &str = "Stack underflow";

impl Vm {
    pub fn load(code: Vec<Slot>) -> Self {
        Vm { ip: 0, end: code.len(), stack: code, frames: vec![] }
    }

    fn sp(&self) -> usize {
        self.stack.len() - 1
    }

    fn sum_size(&self, n: usize) -> Result<usize, &'static str> {
        let mut sp = self.sp();
        for _ in 0..n {
            let size = self.stack.get(sp).ok_or(ERR_STACK_UNDERFLOW)?.size();
            sp = sp.checked_sub(size).ok_or(ERR_STACK_UNDERFLOW)?;
        }
        Ok(self.sp() - sp)
    }

    fn borrow(&self, src: usize, dst: usize) -> Result<Slot, &'static str> {
        match self.stack[src] {
            Int(i) => Ok(Int(i)),
            Var { .. } => Err(ERR_UNRESOLVED_VAR),
            Ref { offset } if offset >= src => Err(ERR_INVALID_REF),
            Ref { offset } => Ok(Ref { offset: dst - (src - offset) }),
            Op(_, _) => Ok(Ref { offset: dst - src }),
        }
    }

    fn push_borrows(&mut self, n: usize) -> Result<(), &'static str> {
        let mut sp: usize = self.sp();
        let top = sp + n;
        self.stack.resize(self.stack.len() + n, Int(0));
        for i in 0..n {
            let slot = self.stack[sp];
            self.stack[top - i] = self.borrow(sp, top - i)?;
            sp -= slot.size();
        }
        Ok(())
    }

    fn pop_optional(&mut self, n: Option<usize>) -> Result<usize, &'static str> {
        todo!()
    }

    fn resolve_slot(&self, sp: usize) -> Result<usize, &'static str> {
        match self.stack[sp] {
            Var { .. } => return Err(ERR_UNRESOLVED_VAR),
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

    fn eval_once(&mut self, comptime: bool) -> Result<(), &'static str> {
        let op = self.stack.get(self.ip).ok_or(ERR_NO_OP)?;
        match *op {
            Int(i) => {
                self.stack.push(Int(i));
                self.ip += 1;
            }
            Ref { offset } => {
                if offset == 0 || offset > self.ip {
                    return Err(ERR_INVALID_REF);
                }
                self.stack.push(self.borrow(self.ip - offset, self.stack.len())?);
                self.ip += 1;
            }
            Var { elem } => {
                self.stack.push(self.borrow(self.resolve_var(elem)?, self.stack.len())?);
                self.ip += 1;
            }
            Op(FuncStart, _) if comptime => todo!(),
            Op(FuncEnd, _) if comptime => todo!(),
            Op(FuncStart, slots) | Op(BlobStart, slots) => {
                self.stack.push(Ref { offset: self.sp() - self.ip - slots });
                self.ip += slots + 2;
            }
            Op(FuncEnd, _) => {
                let CallFrame { floor, ret, .. } = self.frames.pop().ok_or(ERR_NO_CALL_FRAME)?;
                // TODO: run 4 pass compaction
                match self.stack[self.sp()] {
                    Int(i) => {
                        self.stack.truncate(floor);
                        self.stack.push(Int(i));
                    }
                    Ref { offset } if self.sp() - offset < floor => {
                        let compacted = self.sp() - floor;
                        self.stack.truncate(floor);
                        self.stack.push(Ref { offset: offset - compacted });
                    }
                    Op(List { elems }, _) => {
                        let sp = self.sp();
                        self.stack[sp] = Op(List { elems }, sp - floor);
                    }
                    v => todo!("needs full 4 pass compaction: {v:?}"),
                }
                self.ip = ret;
            }
            Op(BlobEnd, _) => return Err(ERR_BLOB_END),
            Op(Call { args }, _) if comptime => {
                self.stack.push(Op(Call { args }, self.sum_size(args)?));
                self.ip += 1;
            }
            Op(Call { args }, _) => {
                let mut slots = self.sum_size(args)?;
                if slots > args {
                    self.push_borrows(args)?;
                    slots += args;
                }
                let sp_f = self.resolve_slot(self.sp() - slots)?;
                let ret = self.ip + 1;
                slots += self.stack[self.sp() - slots].size();
                match self.stack[sp_f] {
                    Op(FuncStart, _) => self.ip = sp_f + 1,
                    Op(FuncEnd, slots) => self.ip = sp_f - slots,
                    _ => return Err(ERR_INVALID_FUNC),
                }
                self.frames.push(CallFrame {
                    floor: self.stack.len() - slots,
                    base: self.stack.len() - args,
                    args,
                    ret,
                });
            }
            Op(Macro { args }, slots) => todo!(),
            Op(List { elems }, _) => {
                let mut slots = self.sum_size(elems)?;
                if slots > elems {
                    self.push_borrows(elems)?;
                    slots += elems;
                }
                self.stack.push(Op(List { elems }, slots));
                self.ip += 1;
            }
            Op(Set { index }, slots) => {
                // TODO: Make sure we make it impossible to create forward-refs
                todo!()
            }
            Op(Get { index }, slots) => {
                // let index = self.pop_optional(index)?;
                // match self.pop()? {
                //     Op(List { elems }, _) if index >= elems => todo!(),
                //     Op(List { elems }, _) => todo!(),
                //     Ref { offset } => todo!(),
                //     v => return Err(ERR_INVALID_LIST),
                // }
                // TODO: the actual logic
                todo!()
            }
            Op(Push { elems }, slots) => todo!(),
            Op(Pop { elems }, slots) => todo!(),
            Op(If, _) => {
                let cond = self.stack.last().ok_or(ERR_STACK_UNDERFLOW)?;
                let Int(cond) = *cond else {
                    return Err(ERR_INVALID_INT);
                };
                let f = self.sp() - 1;
                let t = f - self.stack[f].size();
                let sp_f = self.resolve_slot(f)?;
                let sp_t = self.resolve_slot(t)?;
                match (self.stack[sp_t], self.stack[sp_f]) {
                    (Op(FuncEnd, slots_t), Op(FuncEnd, slots_f)) => {
                        let CallFrame { base, args, .. } =
                            self.frames.last().copied().ok_or(ERR_NO_CALL_FRAME)?;
                        self.frames.push(CallFrame { floor: t, base, args, ret: self.ip + 1 });
                        self.ip = if cond == 0 { sp_f - slots_f } else { sp_t - slots_t };
                    }
                    (_, _) => return Err(ERR_INVALID_FUNC),
                }
            }
            Op(Len, _) => {
                match self.stack[self.sp()] {
                    Ref { offset } => match self.stack[self.sp() - offset] {
                        Op(List { elems }, _) => {
                            self.stack.pop();
                            self.stack.push(Int(elems as i64));
                        }
                        _ => return Err(ERR_INVALID_LIST),
                    },
                    Op(List { elems }, slots) => {
                        self.stack.truncate(self.sp() - slots);
                        self.stack.push(Int(elems as i64));
                    }
                    _ => return Err(ERR_INVALID_LIST),
                }
                self.ip += 1;
            }
            Op(Bin(op), _) => {
                let [.., a, b] = self.stack.as_slice() else {
                    return Err(ERR_STACK_UNDERFLOW);
                };
                let (Int(a), Int(b)) = (*a, *b) else {
                    return Err(ERR_INVALID_INT);
                };
                self.stack.truncate(self.stack.len() - 2);
                self.stack.push(match op {
                    BinOp::Eq if a == b => Int(1),
                    BinOp::Eq => Int(0),
                    BinOp::Add => Int(a.checked_add(b).ok_or(ERR_INT_OVERFLOW)?),
                    BinOp::Sub => Int(a.checked_sub(b).ok_or(ERR_INT_OVERFLOW)?),
                    BinOp::Mul => Int(a.checked_mul(b).ok_or(ERR_INT_OVERFLOW)?),
                });
                self.ip += 1;
            }
        }
        Ok(())
    }

    pub fn run(&mut self) -> Result<(), &'static str> {
        while self.ip != self.end {
            self.eval_once(false)?;
            if self.ip > self.end {
                return Err(ERR_NO_OP);
            }
        }
        Ok(())
    }
}
