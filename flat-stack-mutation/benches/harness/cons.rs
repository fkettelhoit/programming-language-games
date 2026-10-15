//! A traditional functional bytecode VM: heap-allocated cons cells, one
//! reference count per cell, values on a separate operand stack.
//!
//! This is the comparison point for the flat tape. The representation is the
//! textbook one — a list is a chain of `(car, cdr)` cells in logical order,
//! so `prepend`/`head`/`tail` are O(1) and `get`/`set`/`push`/`pop_last` walk
//! the spine. Reclamation is by reference counting, which is the closest
//! traditional analogue of the flat VM's discipline: both are deterministic,
//! neither has a tracing collector.
//!
//! Two update disciplines are measured:
//!
//! - **persistent** (`fip = false`): `set`/`push`/`pop_last` copy the spine up
//!   to the modification point and share the rest. The classic behaviour.
//! - **reuse** (`fip = true`): a cell whose reference count is 1 is updated in
//!   place, and only the shared suffix of the path is copied. This is the
//!   Perceus / "functional but in place" optimisation, and it is the fairest
//!   opponent for an experiment about in-place mutation. It uses exactly the
//!   same last-use information the flat backend uses for `Take`.
//!
//! Work counters count memory traffic in both VMs the same way: one read or
//! write per touched slot/field, including instruction fetch, operand-stack
//! traffic, reference-count updates and cell initialisation.

#![allow(dead_code)]

use std::cmp::max;

use super::lang::Prim;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CVal {
    Int(i64),
    #[default]
    Nil,
    Cell(usize),
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Cell {
    pub rc: u32,
    pub car: CVal,
    pub cdr: CVal,
}

/// How the first operand of a primitive reached the operand stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Arg0 {
    /// A temporary, or a local that was retained: the primitive consumes it.
    Owned,
    /// A local read without retaining, for a primitive that only reads it:
    /// no reference-count traffic at all.
    Borrowed,
}

#[derive(Debug, Clone, Copy)]
pub enum Ins {
    Const(i64),
    /// Read local `slot`, retaining it (the value is about to be owned).
    Local(usize),
    /// Read local `slot` without retaining: the binding's reference is about
    /// to be taken over by the operation below (see `Clear`), or the operand
    /// is only inspected (see `Arg0::Borrowed`).
    LocalRaw(usize),
    /// Hand the binding's reference to the operand stack: the slot is emptied
    /// without releasing, right before the operation that consumes it. The
    /// cons analogue of the flat VM's two-phase `Take` — the binding stays
    /// readable while the sibling operands are evaluated, which is what makes
    /// read-modify-write in place work.
    Clear(usize),
    MakeList(usize),
    Prim(Prim, Arg0),
    Jump(usize),
    JumpIfZero(usize),
    Call {
        entry: usize,
        args: usize,
    },
    TailCall {
        entry: usize,
        args: usize,
    },
    Ret,
    Halt,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Stats {
    pub reads: usize,
    pub writes: usize,
    pub allocs: usize,
    pub frees: usize,
    pub live: usize,
    pub peak_live: usize,
    pub peak_stack: usize,
    pub peak_frames: usize,
    pub steps: usize,
}

impl Stats {
    pub fn work(&self) -> usize {
        self.reads + self.writes
    }
}

#[derive(Debug, Clone, Copy)]
struct Frame {
    base: usize,
    ret: usize,
}

pub struct Vm {
    heap: Vec<Cell>,
    free: Vec<usize>,
    stack: Vec<CVal>,
    frames: Vec<Frame>,
    path: Vec<usize>,
    pub stats: Stats,
    /// Reuse uniquely-owned cells instead of copying them.
    pub fip: bool,
}

const STEP_LIMIT: usize = 2_000_000_000;

impl Vm {
    pub fn new(fip: bool) -> Self {
        Vm {
            heap: vec![],
            free: vec![],
            stack: vec![],
            frames: vec![],
            path: vec![],
            stats: Stats::default(),
            fip,
        }
    }

    // --- heap ------------------------------------------------------------

    fn car(&mut self, i: usize) -> CVal {
        self.stats.reads += 1;
        self.heap[i].car
    }

    fn cdr(&mut self, i: usize) -> CVal {
        self.stats.reads += 1;
        self.heap[i].cdr
    }

    fn set_car(&mut self, i: usize, v: CVal) {
        self.stats.writes += 1;
        self.heap[i].car = v;
    }

    fn set_cdr(&mut self, i: usize, v: CVal) {
        self.stats.writes += 1;
        self.heap[i].cdr = v;
    }

    fn rc(&mut self, i: usize) -> u32 {
        self.stats.reads += 1;
        self.heap[i].rc
    }

    fn retain(&mut self, v: CVal) -> CVal {
        if let CVal::Cell(i) = v {
            self.stats.reads += 1;
            self.stats.writes += 1;
            self.heap[i].rc += 1;
        }
        v
    }

    fn release(&mut self, v: CVal) {
        let mut work = v;
        let mut pending: Vec<CVal> = vec![];
        loop {
            if let CVal::Cell(i) = work {
                self.stats.reads += 1;
                self.stats.writes += 1;
                self.heap[i].rc -= 1;
                if self.heap[i].rc == 0 {
                    let car = self.car(i);
                    let cdr = self.cdr(i);
                    self.stats.writes += 1; // link into the free list
                    self.free.push(i);
                    self.stats.frees += 1;
                    self.stats.live -= 1;
                    if let CVal::Cell(_) = car {
                        pending.push(car);
                    }
                    work = cdr;
                    continue;
                }
            }
            match pending.pop() {
                Some(v) => work = v,
                None => return,
            }
        }
    }

    fn alloc(&mut self, car: CVal, cdr: CVal) -> CVal {
        self.stats.allocs += 1;
        self.stats.live += 1;
        self.stats.peak_live = max(self.stats.peak_live, self.stats.live);
        self.stats.writes += 3; // rc, car, cdr
        let i = match self.free.pop() {
            Some(i) => {
                self.stats.reads += 1;
                i
            }
            None => {
                self.heap.push(Cell::default());
                self.heap.len() - 1
            }
        };
        self.heap[i] = Cell { rc: 1, car, cdr };
        CVal::Cell(i)
    }

    // --- operand stack ---------------------------------------------------

    fn push(&mut self, v: CVal) {
        self.stats.writes += 1;
        self.stack.push(v);
        self.stats.peak_stack = max(self.stats.peak_stack, self.stack.len());
    }

    fn pop(&mut self) -> Result<CVal, String> {
        self.stats.reads += 1;
        self.stack.pop().ok_or_else(|| "operand stack underflow".to_string())
    }

    fn pop_int(&mut self) -> Result<i64, String> {
        match self.pop()? {
            CVal::Int(i) => Ok(i),
            v => Err(format!("expected an int, got {v:?}")),
        }
    }

    // --- list primitives -------------------------------------------------

    fn as_cell(v: CVal) -> Result<usize, String> {
        match v {
            CVal::Cell(i) => Ok(i),
            v => Err(format!("expected a list cell, got {v:?}")),
        }
    }

    /// Fill `self.path` with the cells of `l` (at most `limit`), returning the
    /// value that follows the last one.
    fn walk(&mut self, l: CVal, limit: usize) -> Result<CVal, String> {
        self.path.clear();
        let mut cur = l;
        while self.path.len() < limit {
            let CVal::Cell(c) = cur else { break };
            self.path.push(c);
            cur = self.cdr(c);
        }
        Ok(cur)
    }

    fn len_of(&mut self, l: CVal) -> usize {
        let mut n = 0;
        let mut cur = l;
        while let CVal::Cell(c) = cur {
            n += 1;
            cur = self.cdr(c);
        }
        n
    }

    fn get_at(&mut self, l: CVal, i: usize) -> Result<CVal, String> {
        let mut cur = l;
        for _ in 0..i {
            let c = Self::as_cell(cur)?;
            cur = self.cdr(c);
        }
        let c = Self::as_cell(cur)?;
        let v = self.car(c);
        Ok(self.retain(v))
    }

    /// `l` with element `i` replaced by `v`. Consumes one reference to `l` and
    /// the reference to `v`.
    fn set_at(&mut self, l: CVal, i: usize, v: CVal) -> Result<CVal, String> {
        let rest = self.walk(l, i + 1)?;
        if self.path.len() != i + 1 {
            self.release(l);
            self.release(v);
            return Err("set index out of bounds".into());
        }
        let mut split = 0;
        if self.fip {
            while split <= i && self.rc(self.path[split]) == 1 {
                split += 1;
            }
        }
        if split > i {
            let cell = self.path[i];
            let old = self.car(cell);
            self.set_car(cell, v);
            self.release(old);
            return Ok(l);
        }
        let mut new = self.retain(rest);
        for k in (split..=i).rev() {
            let elem = if k == i {
                v
            } else {
                let c = self.car(self.path[k]);
                self.retain(c)
            };
            new = self.alloc(elem, new);
        }
        self.reattach(l, split, new)
    }

    /// `l` with `v` appended at the end.
    fn push_end(&mut self, l: CVal, v: CVal) -> Result<CVal, String> {
        if l == CVal::Nil {
            return Ok(self.alloc(v, CVal::Nil));
        }
        self.walk(l, usize::MAX)?;
        let n = self.path.len();
        let mut split = 0;
        if self.fip {
            while split < n && self.rc(self.path[split]) == 1 {
                split += 1;
            }
        }
        if split == n {
            let tail = self.alloc(v, CVal::Nil);
            self.set_cdr(self.path[n - 1], tail);
            return Ok(l);
        }
        let mut new = self.alloc(v, CVal::Nil);
        for k in (split..n).rev() {
            let c = self.car(self.path[k]);
            let c = self.retain(c);
            new = self.alloc(c, new);
        }
        self.reattach(l, split, new)
    }

    /// `l` without its last element.
    fn pop_end(&mut self, l: CVal) -> Result<CVal, String> {
        self.walk(l, usize::MAX)?;
        let n = self.path.len();
        if n == 0 {
            return Err("pop_last of an empty list".into());
        }
        if n == 1 {
            self.release(l);
            return Ok(CVal::Nil);
        }
        let mut split = 0;
        if self.fip {
            while split < n - 1 && self.rc(self.path[split]) == 1 {
                split += 1;
            }
        }
        if split == n - 1 {
            let cell = self.path[n - 2];
            let old = self.cdr(cell);
            self.set_cdr(cell, CVal::Nil);
            self.release(old);
            return Ok(l);
        }
        let mut new = CVal::Nil;
        for k in (split..n - 1).rev() {
            let c = self.car(self.path[k]);
            let c = self.retain(c);
            new = self.alloc(c, new);
        }
        self.reattach(l, split, new)
    }

    /// Hang a freshly copied suffix off the last uniquely-owned cell, or
    /// return it as the new head when nothing was owned.
    fn reattach(&mut self, l: CVal, split: usize, new: CVal) -> Result<CVal, String> {
        if split == 0 {
            self.release(l);
            Ok(new)
        } else {
            let cell = self.path[split - 1];
            let old = self.cdr(cell);
            self.set_cdr(cell, new);
            self.release(old);
            Ok(l)
        }
    }

    // --- interpreter -----------------------------------------------------

    pub fn run(&mut self, code: &[Ins], entry: usize) -> Result<CVal, String> {
        let mut ip = entry;
        self.frames.push(Frame { base: 0, ret: usize::MAX });
        loop {
            self.stats.steps += 1;
            if self.stats.steps > STEP_LIMIT {
                return Err("step limit exceeded".into());
            }
            self.stats.reads += 1; // instruction fetch
            let ins = code[ip];
            ip += 1;
            let base = self.frames.last().expect("a frame").base;
            match ins {
                Ins::Const(i) => self.push(CVal::Int(i)),
                Ins::Local(slot) => {
                    self.stats.reads += 1;
                    let v = self.stack[base + slot];
                    let v = self.retain(v);
                    self.push(v);
                }
                Ins::LocalRaw(slot) => {
                    self.stats.reads += 1;
                    let v = self.stack[base + slot];
                    self.push(v);
                }
                Ins::MakeList(n) => {
                    let mut acc = CVal::Nil;
                    for _ in 0..n {
                        let v = self.pop()?;
                        acc = self.alloc(v, acc);
                    }
                    self.push(acc);
                }
                Ins::Clear(slot) => {
                    self.stats.writes += 1;
                    self.stack[base + slot] = CVal::Nil;
                }
                Ins::Prim(p, arg0) => self.prim(p, arg0)?,
                Ins::Jump(t) => ip = t,
                Ins::JumpIfZero(t) => {
                    if self.pop_int()? == 0 {
                        ip = t;
                    }
                }
                Ins::Call { entry, args } => {
                    let b = self.stack.len() - args;
                    self.stats.writes += 2;
                    self.frames.push(Frame { base: b, ret: ip });
                    self.stats.peak_frames = max(self.stats.peak_frames, self.frames.len());
                    ip = entry;
                }
                Ins::TailCall { entry, args } => {
                    let top = self.stack.len() - args;
                    for i in base..top {
                        self.stats.reads += 1;
                        let v = self.stack[i];
                        self.release(v);
                    }
                    if top > base {
                        self.stats.reads += args;
                        self.stats.writes += args;
                        self.stack.copy_within(top.., base);
                        self.stack.truncate(base + args);
                    }
                    ip = entry;
                }
                Ins::Ret => {
                    let v = self.pop()?;
                    self.stats.reads += 2;
                    let frame = self.frames.pop().expect("a frame");
                    for i in frame.base..self.stack.len() {
                        self.stats.reads += 1;
                        let v = self.stack[i];
                        self.release(v);
                    }
                    self.stack.truncate(frame.base);
                    self.push(v);
                    ip = frame.ret;
                }
                Ins::Halt => return self.pop(),
            }
        }
    }

    fn prim(&mut self, p: Prim, arg0: Arg0) -> Result<(), String> {
        // The list operand of every list primitive is its first argument, so
        // it is the deepest on the operand stack.
        match p {
            Prim::Add | Prim::Sub | Prim::Mul | Prim::Div | Prim::Rem | Prim::Eq | Prim::Lt => {
                let b = self.pop_int()?;
                let a = self.pop_int()?;
                let v = match p {
                    Prim::Add => a.checked_add(b).ok_or("int overflow")?,
                    Prim::Sub => a.checked_sub(b).ok_or("int overflow")?,
                    Prim::Mul => a.checked_mul(b).ok_or("int overflow")?,
                    Prim::Div => a.checked_div(b).ok_or("division by zero")?,
                    Prim::Rem => a.checked_rem(b).ok_or("division by zero")?,
                    Prim::Eq => (a == b) as i64,
                    Prim::Lt => (a < b) as i64,
                    _ => unreachable!(),
                };
                self.push(CVal::Int(v));
                return Ok(());
            }
            _ => {}
        }
        match p {
            Prim::Get => {
                let i = self.pop_int()?;
                let l = self.pop()?;
                let v = self.get_at(l, i as usize)?;
                self.consume(l, arg0);
                self.push(v);
            }
            Prim::Head => {
                let l = self.pop()?;
                let c = Self::as_cell(l)?;
                let v = self.car(c);
                let v = self.retain(v);
                self.consume(l, arg0);
                self.push(v);
            }
            Prim::Tail => {
                let l = self.pop()?;
                let c = Self::as_cell(l)?;
                let v = self.cdr(c);
                let v = self.retain(v);
                self.consume(l, arg0);
                self.push(v);
            }
            Prim::Len => {
                let l = self.pop()?;
                let n = self.len_of(l);
                self.consume(l, arg0);
                self.push(CVal::Int(n as i64));
            }
            Prim::IsNil => {
                let l = self.pop()?;
                let v = (l == CVal::Nil) as i64;
                self.consume(l, arg0);
                self.push(CVal::Int(v));
            }
            Prim::Prepend => {
                let l = self.pop()?;
                let e = self.pop()?;
                let v = self.alloc(e, l);
                self.push(v);
            }
            Prim::Set => {
                let i = self.pop_int()?;
                let v = self.pop()?;
                let l = self.pop()?;
                let new = self.set_at(l, i as usize, v)?;
                self.push(new);
            }
            Prim::Push => {
                let e = self.pop()?;
                let l = self.pop()?;
                let new = self.push_end(l, e)?;
                self.push(new);
            }
            Prim::PopLast => {
                let l = self.pop()?;
                let new = self.pop_end(l)?;
                self.push(new);
            }
            Prim::List => return Err("Prim::List is compiled to MakeList".into()),
            _ => unreachable!(),
        }
        Ok(())
    }

    /// A read-only primitive is done with its operand: release it unless the
    /// operand was borrowed from a binding that still owns it.
    fn consume(&mut self, l: CVal, arg0: Arg0) {
        if arg0 == Arg0::Owned {
            self.release(l);
        }
    }

    // --- inspection ------------------------------------------------------

    pub fn to_vec(&self, v: CVal) -> Vec<CVal> {
        let mut out = vec![];
        let mut cur = v;
        while let CVal::Cell(c) = cur {
            out.push(self.heap[c].car);
            cur = self.heap[c].cdr;
        }
        out
    }
}
