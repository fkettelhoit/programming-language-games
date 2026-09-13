#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Slot {
    pub op: Op,
    pub mark: bool,
    pub shift: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Op {
    Moved,
    Int(i64),
    Var { elem: usize },
    Take { elem: usize },
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
    Pop { elems: usize },
    Set,
    Get,
    If,
    Len,
    Bin(BinOp),
}

impl SizedOp {
    fn arity(self) -> usize {
        match self {
            Call { args: n, .. } | Push { elems: n } => n + 1,
            List { elems } => elems,
            Set | If => 3,
            Get | Bin(_) => 2,
            Pop { .. } | Len => 1,
            BlobStart | BlobEnd | FnStart | FnEnd { .. } => 0,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BinOp {
    Eq,
    Lt,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

use std::{cmp::max, ops::Range};

use Op::*;
use SizedOp::*;

impl From<Op> for Slot {
    fn from(op: Op) -> Self {
        Slot { op, shift: 0, mark: false }
    }
}

impl Op {
    fn size(&self) -> usize {
        match self {
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

#[derive(Debug, Clone, Copy, Default)]
pub struct Stats {
    pub reads: usize,
    pub writes: usize,
}

#[derive(Debug)]
pub struct Vm {
    pub ip: usize,
    pub end: usize,
    pub stack: Vec<Slot>,
    pub frames: Vec<CallFrame>,
    pub stats: Stats,
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
const ERR_USE_AFTER_MOVE: &str = "Use after move";

impl Vm {
    pub fn load(code: Vec<Op>) -> Self {
        let stack: Vec<_> = code.into_iter().map(|op| Slot { op, shift: 0, mark: false }).collect();
        Vm { ip: 0, end: stack.len(), stack, frames: vec![], stats: Stats::default() }
    }

    fn sp(&self) -> usize {
        self.stack.len() - 1
    }

    fn slot(&mut self, sp: usize) -> Result<Slot, &'static str> {
        self.stats.reads += 1;
        self.stack.get(sp).ok_or(ERR_UNDERFLOW).copied()
    }

    fn op(&mut self, sp: usize) -> Result<Op, &'static str> {
        Ok(self.slot(sp)?.op)
    }

    fn write_slot(&mut self, sp: usize, slot: Slot) -> Result<(), &'static str> {
        self.stats.writes += 1;
        *self.stack.get_mut(sp).ok_or(ERR_UNDERFLOW)? = slot;
        Ok(())
    }

    fn write(&mut self, sp: usize, op: Op) -> Result<(), &'static str> {
        self.write_slot(sp, op.into())
    }

    fn slide(&mut self, sp: usize, shift: usize, op: Op) -> Result<(), &'static str> {
        self.stats.writes += 2;
        let shifted = self.stack.get_mut(sp - shift).ok_or(ERR_UNDERFLOW)?;
        *shifted = Slot { op, shift: shifted.shift, mark: false };
        *self.stack.get_mut(sp).ok_or(ERR_UNDERFLOW)? = Slot { op, shift, mark: false };
        Ok(())
    }

    fn push(&mut self, op: Op) {
        self.stats.writes += 1;
        self.stack.push(op.into())
    }

    fn sum_size(&mut self, src: usize, n: usize) -> Result<usize, &'static str> {
        let mut sp = src;
        for _ in 0..n {
            let size = self.op(sp)?.size();
            sp = sp.checked_sub(size).ok_or(ERR_UNDERFLOW)?;
        }
        Ok(src - sp)
    }

    fn borrow(&mut self, src: usize, dst: usize) -> Result<Op, &'static str> {
        Ok(match self.op(src)? {
            Moved | Take { .. } => return Err(ERR_USE_AFTER_MOVE),
            v @ (Int(_) | Var { .. } | Sized(List { elems: 0 }, 0)) => v,
            Ref { offset } if offset > src => return Err(ERR_INVALID_REF),
            Ref { offset } => Ref { offset: dst - (src - offset) },
            Sized(_, _) => Ref { offset: dst - src },
        })
    }

    fn write_borrow(&mut self, src: usize, dst: usize) -> Result<(), &'static str> {
        let borrow = self.borrow(src, dst)?;
        self.write(dst, borrow)
    }

    fn push_borrows(&mut self, mut src: usize, n: usize, take: bool) -> Result<(), &'static str> {
        let top = self.stack.len() - 1 + n;
        self.stack.resize(self.stack.len() + n, Int(0).into());
        for i in 0..n {
            let op = self.op(src)?;
            self.write_borrow(src, top - i)?;
            if take && let Ref { .. } = op {
                self.write(src, Moved)?;
            }
            src = src.checked_sub(op.size()).ok_or(ERR_UNDERFLOW)?;
        }
        Ok(())
    }

    fn resolve_slot(&mut self, sp: usize) -> Result<usize, &'static str> {
        match self.op(sp)? {
            Moved => return Err(ERR_USE_AFTER_MOVE),
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
        for sp in sp + 1 - self.op(sp)?.size()..=sp {
            self.stack.get_mut(sp).ok_or(ERR_UNDERFLOW)?.mark = true;
        }
        Ok(())
    }

    fn mark_and_compact(&mut self, floor: usize, top: usize) -> Result<usize, &'static str> {
        // pass 1: mark (floor <- top)
        for sp in (floor..=top).rev() {
            if let Slot { op: Ref { offset }, mark: true, .. } = self.slot(sp)? {
                let r = sp.checked_sub(offset).ok_or(ERR_INVALID_REF)?;
                if r >= floor && r < sp {
                    self.mark(r)?;
                }
            }
        }
        // pass 2: compact (floor -> top)
        let mut gap = 0;
        for sp in floor..=top {
            let mut slot = self.slot(sp)?;
            if slot.mark {
                if gap > 0 {
                    if let Ref { offset } = slot.op {
                        let shift =
                            if sp - offset >= floor { self.slot(sp - offset)?.shift } else { 0 };
                        let src = sp - gap;
                        let dst = sp - offset - shift;
                        slot.op = Ref { offset: src - dst };
                    }
                    self.slide(sp, gap, slot.op)?;
                } else {
                    self.write(sp, slot.op)?;
                }
            } else {
                gap += 1;
            }
        }
        Ok(gap)
    }

    fn gc_block(&mut self, block: Range<usize>, track: usize) -> Result<usize, &'static str> {
        for sp in block.end..=self.sp() {
            self.stack.get_mut(sp).ok_or(ERR_UNDERFLOW)?.mark = true;
        }
        let gap = self.mark_and_compact(block.start, self.sp())?;
        let track = if track >= block.start { track - self.slot(track)?.shift } else { track };
        self.stack.truncate(self.stack.len() - gap);
        Ok(track)
    }

    fn gc_until(&mut self, floor: usize) -> Result<(), &'static str> {
        // resolve the return value first
        let Some(top) = self.stack.len().checked_sub(1) else { return Ok(()) };
        let ret = self.resolve_slot(top)?;
        match self.op(ret)? {
            Sized(List { elems: n }, _) if self.sum_size(ret - 1, n)? == n => {
                for sp in ret - n..=ret {
                    self.stack.get_mut(sp).ok_or(ERR_UNDERFLOW)?.mark = true;
                }
            }
            _ => self.mark(ret)?,
        }
        let gap = self.mark_and_compact(floor, ret)?;
        self.stack.truncate(ret + 1 - gap);
        match self.stack.last_mut().ok_or(ERR_UNDERFLOW)? {
            Slot { op: Sized(FnEnd { .. } | BlobEnd, _), .. } => {}
            Slot { op: Sized(_, slots), .. } => *slots = (ret - gap) - floor,
            _ => {}
        }
        Ok(())
    }

    fn live_prefix(&mut self, block: Range<usize>) -> Result<(usize, usize), &'static str> {
        let mut sp = self.sp();
        let mut max_live = block.start;
        let mut sum_live = 0;
        while sp >= block.end {
            match self.op(sp)? {
                Ref { offset } if block.contains(&(sp - offset)) => {
                    max_live = max(max_live, sp - offset + 1);
                    sum_live += self.op(sp - offset).map_err(|_| ERR_INVALID_REF)?.size();
                }
                Sized(BlobEnd, slots) => sp -= slots,
                _ => {}
            }
            sp = sp.checked_sub(1).ok_or(ERR_UNDERFLOW)?;
        }
        Ok((max_live, sum_live))
    }

    fn slide_block(&mut self, block: Range<usize>, keep: usize) -> Result<usize, &'static str> {
        let shift = block.end - keep;
        if shift == 0 {
            return Ok(0);
        }
        let mut sp = self.sp();
        while sp >= block.end {
            match self.op(sp)? {
                Ref { offset } if sp - offset < block.end => {
                    self.write(sp, Ref { offset: offset - shift })?
                }
                Sized(BlobEnd, slots) => sp -= slots,
                _ => {}
            }
            sp = sp.checked_sub(1).ok_or(ERR_UNDERFLOW)?;
        }
        self.stack.drain(keep..block.end);
        Ok(shift)
    }

    fn gc_tail(&mut self, from: usize, to: usize, track: usize) -> Result<usize, &'static str> {
        let (max_live, sum_live) = self.live_prefix(from..to)?;
        if max_live - from > 2 * sum_live {
            self.gc_block(from..to, track)
        } else {
            let shift = self.slide_block(from..to, max_live)?;
            Ok(if track >= to { track - shift } else { track })
        }
    }

    fn grow(&mut self, from: usize, by: usize) -> Result<(), &'static str> {
        let len = self.stack.len();
        self.stack.resize(len + by, Moved.into());
        for sp in (from..len).rev() {
            let op = match self.op(sp)? {
                Ref { offset } if sp - offset < from => Ref { offset: offset + by },
                op => op,
            };
            self.write(sp + by, op)?;
        }
        for f in &mut self.frames {
            f.floor += if f.floor >= from { by } else { 0 };
            f.base += if f.base >= from { by } else { 0 };
            if let Some(ret) = &mut f.ret {
                *ret += if *ret >= from { by } else { 0 };
            }
        }
        self.ip += if self.ip >= from { by } else { 0 };
        Ok(())
    }

    fn pop_tail_frames(&mut self) -> Result<CallFrame, &'static str> {
        let mut f = self.frames.pop().ok_or(ERR_NO_CALL_FRAME)?;
        while let Some(r) = f.ret {
            if !matches!(self.op(r), Ok(Sized(FnEnd { .. }, _))) {
                break;
            }
            match self.frames.last() {
                Some(g) if g.ret.is_some() && !g.is_deferred => {
                    f = self.frames.pop().ok_or(ERR_NO_CALL_FRAME)?;
                }
                _ => break,
            }
        }
        Ok(f)
    }

    fn is_unique(&mut self, range: Range<usize>) -> Result<bool, &'static str> {
        let floor = range.start;
        for sp in range.rev() {
            if let Ref { offset } = self.op(sp)? {
                if sp - offset == floor {
                    return Ok(false);
                }
            }
        }
        return Ok(true);
    }

    fn claim(&mut self, sp: usize) -> Result<usize, &'static str> {
        if let Take { elem } = self.op(sp)? {
            let sp_var = self.resolve_var(elem)?;
            match self.op(sp_var)? {
                Var { .. } | Take { .. } => {}
                _ => {
                    self.write_borrow(sp_var, sp)?;
                    self.write(sp_var, Moved)?;
                }
            }
        }
        self.resolve_slot(sp)
    }

    fn claim_operands(&mut self, op: SizedOp) -> Result<(), &'static str> {
        let mut sp = self.sp();
        for _ in 0..op.arity() {
            self.claim(sp)?;
            sp = sp.checked_sub(self.op(sp)?.size()).ok_or(ERR_UNDERFLOW)?;
        }
        Ok(())
    }

    fn is_fwd_ref(&mut self, sp_op: usize, top: usize) -> bool {
        match self.op(sp_op) {
            Ok(Ref { offset }) => sp_op - offset >= top,
            Ok(Sized(_, _)) => true,
            _ => false,
        }
    }

    fn has_comptime(&mut self, slots: usize) -> Result<bool, &'static str> {
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

    fn is_value(&mut self, sp: usize) -> Result<bool, &'static str> {
        Ok(match self.op(sp)? {
            Int(_) | Sized(BlobEnd | FnEnd { .. }, _) => true,
            Sized(List { elems }, _) if self.sum_size(sp - 1, elems)? == elems => true,
            _ => false,
        })
    }

    fn is_deferred(&self) -> bool {
        self.frames.last().map(|f| f.is_deferred).unwrap_or(true)
    }

    fn defer(&mut self, op: SizedOp) -> Result<bool, &'static str> {
        let mut sp = self.sp();
        let mut is_unresolved = false;
        let allow_vars = matches!(op, Call { .. });
        for _ in 0..op.arity() {
            match self.op(sp)? {
                Var { .. } if allow_vars => {}
                Take { elem } => {
                    let sp = self.resolve_slot(self.resolve_var(elem)?)?;
                    if !self.is_value(sp)? {
                        is_unresolved = true;
                    }
                }
                _ => {
                    let sp = self.resolve_slot(sp)?;
                    if !self.is_value(sp)? {
                        is_unresolved = true;
                    }
                }
            }
            sp = sp.checked_sub(self.op(sp)?.size()).ok_or(ERR_UNDERFLOW)?;
        }
        if is_unresolved {
            self.push(Sized(op, self.sp() - sp));
            self.ip += 1;
        }
        Ok(is_unresolved)
    }

    fn eval_once(&mut self, comptime: bool) -> Result<(), &'static str> {
        match self.op(self.ip).map_err(|_| ERR_NO_OP)? {
            v @ (Moved | Int(_)) => {
                self.push(v);
                self.ip += 1;
            }
            Take { elem } => {
                self.resolve_var(elem)?; // to validate the index
                self.push(Take { elem });
                self.ip += 1;
            }
            Var { elem } => {
                let borrow = self.borrow(self.resolve_var(elem)?, self.stack.len())?;
                self.push(borrow);
                self.ip += 1;
            }
            Ref { offset } => {
                if offset == 0 || offset > self.ip {
                    return Err(ERR_INVALID_REF);
                }
                let borrow = self.borrow(self.ip - offset, self.stack.len())?;
                self.push(borrow);
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
                self.claim(self.sp())?;
                let CallFrame { floor, ret, .. } = self.frames.pop().ok_or(ERR_NO_CALL_FRAME)?;
                let sp = self.sp();
                let threatened = sp - floor;
                match self.op(sp)? {
                    v @ (Int(_) | Var { .. } | Take { .. }) => {
                        self.stack.truncate(floor);
                        self.push(v);
                    }
                    Ref { offset } if sp - offset < floor => {
                        self.stack.truncate(floor);
                        self.push(Ref { offset: offset - threatened });
                    }
                    Sized(List { elems }, slots) if threatened - slots <= slots => {
                        self.write(sp, Sized(List { elems }, sp - floor))?;
                    }
                    _ => self.gc_until(floor)?,
                }
                match ret {
                    Some(ret) => self.ip = ret,
                    None => {
                        let slots = self.stack.len() - floor;
                        self.write(floor - 1, Sized(FnStart, slots))?;
                        self.push(Sized(FnEnd { args }, slots));
                        self.ip += 1;
                    }
                }
            }
            Sized(BlobEnd, _) => return Err(ERR_BLOB_END),
            Sized(op @ Call { .. }, _) if comptime && self.defer(op)? => {}
            Sized(Call { args, comptime: false }, _) if comptime && self.is_deferred() => {
                let slots_args = self.sum_size(self.sp(), args)?;
                let sp_op = self.sp() - slots_args;
                let slots = slots_args + self.op(sp_op)?.size();
                self.push(Sized(Call { args, comptime: false }, slots));
                self.ip += 1;
            }
            Sized(op @ Call { args, comptime: f_ct }, _) => {
                self.claim_operands(op)?;
                let sp_args = self.sp();
                let slots_args = self.sum_size(sp_args, args)?;
                let sp_op = sp_args - slots_args;
                let slots_op = self.op(sp_op)?.size();
                let sp_f = self.resolve_slot(sp_op)?;
                let ret = Some(self.ip + 1);
                match (self.op(sp_f)?, self.op(self.ip + 1)?) {
                    (Sized(FnEnd { args: a }, _), _) if args != a => return Err(ERR_INVALID_ARITY),
                    (Sized(FnEnd { .. }, slots_f), _) => {
                        if slots_args > args {
                            self.push_borrows(sp_args, args, true)?;
                        }
                        let (sp_f, frame) = match (self.op(self.ip + 1)?, self.frames.last()) {
                            (Sized(FnEnd { .. }, _), Some(frame)) if !frame.is_deferred => {
                                let frame = self.pop_tail_frames()?;
                                let call_start = sp_op - slots_op + 1;
                                let sp_f = self.gc_tail(frame.floor, call_start, sp_f)?;
                                (sp_f, CallFrame { base: self.stack.len() - args, args, ..frame })
                            }
                            _ => {
                                let base = self.stack.len() - args;
                                let floor = sp_op - slots_op + 1;
                                let is_deferred = false;
                                (sp_f, CallFrame { floor, base, args, ret, is_deferred })
                            }
                        };
                        self.frames.push(frame);
                        self.ip = sp_f.checked_sub(slots_f).ok_or(ERR_UNDERFLOW)?;
                    }
                    (Sized(List { elems }, _), _) if elems > 0 => {
                        // closure = [FnEnd, <arg0>, <arg1>, ...]
                        let sp_code = self.resolve_slot(sp_f - elems)?;
                        match self.op(sp_code)? {
                            Sized(FnEnd { args: a }, _) if elems - 1 + args != a => {
                                return Err(ERR_INVALID_ARITY);
                            }
                            Sized(FnEnd { .. }, slots_code) => {
                                self.push_borrows(sp_f - 1, elems - 1, sp_f == sp_op)?;
                                self.push_borrows(sp_args, args, true)?;
                                let arity = elems - 1 + args;
                                let (sp_code, frame) =
                                    match (self.op(self.ip + 1)?, self.frames.last()) {
                                        (Sized(FnEnd { .. }, _), Some(frame))
                                            if !frame.is_deferred =>
                                        {
                                            let frame = self.pop_tail_frames()?;
                                            let call_start = sp_op - slots_op + 1;
                                            let sp_code =
                                                self.gc_tail(frame.floor, call_start, sp_code)?;
                                            let frame = CallFrame {
                                                base: self.stack.len() - arity,
                                                args: arity,
                                                ..frame
                                            };
                                            (sp_code, frame)
                                        }
                                        _ => {
                                            let frame = CallFrame {
                                                floor: sp_op - slots_op + 1,
                                                base: self.stack.len() - arity,
                                                args: arity,
                                                ret,
                                                is_deferred: false,
                                            };
                                            (sp_code, frame)
                                        }
                                    };
                                self.frames.push(frame);
                                self.ip = sp_code.checked_sub(slots_code).ok_or(ERR_UNDERFLOW)?;
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
            Sized(op @ List { .. }, _) if comptime && self.defer(op)? => {}
            Sized(op @ List { elems }, _) => {
                self.claim_operands(op)?;
                let mut slots = self.sum_size(self.sp(), elems)?;
                if slots > elems {
                    self.push_borrows(self.sp(), elems, true)?;
                    slots += elems;
                }
                self.push(Sized(List { elems }, slots));
                self.ip += 1;
            }
            Sized(op @ Push { .. }, _) if comptime && self.defer(op)? => {}
            Sized(op @ Push { elems: n }, _) => {
                self.claim_operands(op)?;
                let sp = self.sp();
                let slots_tail = self.sum_size(sp, n as usize)?;
                let sp_op = sp - slots_tail;
                let sp_list = self.resolve_slot(sp_op)?;
                let Sized(List { elems }, slots_old) = self.op(sp_list)? else {
                    return Err(ERR_INVALID_LIST);
                };
                let mutable = slots_tail == n
                    && (sp_op + 1..=sp).all(|s| !self.is_fwd_ref(s, sp_list))
                    && (sp_list == sp_op
                        || sp_op - sp_list <= elems && self.is_unique(sp_list..sp_op)?);
                if mutable {
                    let shift = if sp_list == sp_op { 0 } else { n };
                    self.grow(sp_list, shift)?;
                    for i in 0..n {
                        self.write_borrow(sp_op + shift + i + 1, sp_list + i)?;
                    }
                    self.write(sp_list + n, Sized(List { elems: elems + n }, slots_old + n))?;
                    self.stack.truncate(sp_op + n + 1);
                } else {
                    self.push_borrows(sp_list - 1, elems, sp_list == sp_op)?;
                    self.push_borrows(sp, n as usize, true)?;
                    let base = if sp_list == sp_op { sp_list - slots_old } else { sp_op };
                    self.push(Sized(List { elems: elems + n as usize }, self.stack.len() - base));
                    self.write(sp_op, Moved)?;
                }
                self.ip += 1;
            }
            Sized(op @ Pop { .. }, _) if comptime && self.defer(op)? => {}
            Sized(op @ Pop { elems: n }, _) => {
                self.claim_operands(op)?;
                let sp_op = self.sp();
                let sp_list = self.resolve_slot(sp_op)?;
                let Sized(List { elems }, slots_old) = self.op(sp_list)? else {
                    return Err(ERR_INVALID_LIST);
                };
                if n > elems {
                    return Err(ERR_INDEX_OUT_OF_BOUNDS);
                }
                let slots_popped = self.sum_size(sp_list - 1, n)?;
                let sp_rest_last = sp_list - 1 - slots_popped;

                if sp_list == sp_op {
                    self.stack.truncate(sp_rest_last + 1);
                    self.push(Sized(List { elems: elems - n }, slots_old - slots_popped));
                } else if sp_op - sp_list <= elems && self.is_unique(sp_list..sp_op)? {
                    for sp in sp_list - n + 1..=sp_list {
                        self.write(sp, Moved)?;
                    }
                    self.write(
                        sp_list - n,
                        Sized(List { elems: elems - n }, slots_old - slots_popped),
                    )?;
                    self.write(sp_op, Ref { offset: sp_op - (sp_list - n) })?;
                } else {
                    self.push_borrows(sp_rest_last, elems - n, false)?;
                    self.push(Sized(List { elems: elems - n }, self.stack.len() - sp_op));
                    self.write(sp_op, Moved)?;
                }
                self.ip += 1;
            }
            Sized(op @ Set, _) if comptime && self.defer(op)? => {}
            Sized(op @ Set, _) => {
                self.claim_operands(op)?;
                let Int(i) = self.op(self.sp())? else {
                    return Err(ERR_INVALID_INT);
                };
                let sp_elem = self.sp() - 1;
                let elem_size = self.op(sp_elem)?.size();
                let sp_op = self.sp() - 1 - elem_size;
                let sp_list = self.resolve_slot(sp_op)?;
                let Sized(List { elems }, slots_old) = self.op(sp_list)? else {
                    return Err(ERR_INVALID_LIST);
                };
                if i < 0 || i as usize >= elems {
                    return Err(ERR_INDEX_OUT_OF_BOUNDS);
                }
                let sp_i = sp_list - elems + i as usize;
                if sp_op - sp_list <= elems
                    && self.is_unique(sp_list..sp_op)?
                    && !self.is_fwd_ref(sp_elem, sp_i)
                {
                    self.write_borrow(sp_elem, sp_i)?;
                    self.stack.truncate(sp_op + 1);
                } else {
                    self.push_borrows(sp_list - 1, elems, sp_list == sp_op)?;
                    let sp_i = self.stack.len() - elems + i as usize;
                    self.write_borrow(sp_elem, sp_i)?;
                    let base = if sp_list == sp_op { sp_list - slots_old } else { sp_op };
                    self.push(Sized(List { elems }, self.stack.len() - base));
                    self.write(sp_op, Moved)?;
                }
                self.ip += 1;
            }
            Sized(op @ Get, _) if comptime && self.defer(op)? => {}
            Sized(op @ Get, _) => {
                self.claim_operands(op)?;
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
                    self.write_borrow(sp_elem, sp_op)?;
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
                            self.write(sp_ref, Ref { offset: sp_ref - (sp_elem - offset) })?;
                            self.gc_until(base)?;
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
            Sized(op @ If, _) if comptime && self.defer(op)? => {}
            Sized(op @ If, _) => {
                self.claim_operands(op)?;
                let cond = self.op(self.sp())?;
                let Int(cond) = cond else {
                    return Err(ERR_INVALID_INT);
                };
                let f = self.sp() - 1;
                let size_f = self.op(f)?.size();
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
            Sized(op @ Len, _) if comptime && self.defer(op)? => {}
            Sized(op @ Len, _) => {
                self.claim_operands(op)?;
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
            Sized(op @ Bin(_), _) if comptime && self.defer(op)? => {}
            Sized(op @ Bin(bin_op), _) => {
                self.claim_operands(op)?;
                let [.., a, b] = self.stack.as_slice() else {
                    return Err(ERR_UNDERFLOW);
                };
                let (Int(a), Int(b)) = (a.op, b.op) else {
                    return Err(ERR_INVALID_INT);
                };
                let slot = match bin_op {
                    BinOp::Eq => Int(if a == b { 1 } else { 0 }),
                    BinOp::Lt => Int(if a < b { 1 } else { 0 }),
                    BinOp::Add => Int(a.checked_add(b).ok_or(ERR_INT_OVERFLOW)?),
                    BinOp::Sub => Int(a.checked_sub(b).ok_or(ERR_INT_OVERFLOW)?),
                    BinOp::Mul => Int(a.checked_mul(b).ok_or(ERR_INT_OVERFLOW)?),
                    BinOp::Div => Int(a.checked_div(b).ok_or(ERR_INT_OVERFLOW)?),
                    BinOp::Rem => Int(a.checked_rem(b).ok_or(ERR_INT_OVERFLOW)?),
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
        self.gc_until(0)
    }
}
