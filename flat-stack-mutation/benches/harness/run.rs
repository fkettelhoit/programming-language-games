//! Running a program on a backend and measuring it.
//!
//! Time is measured two ways. The primary metric is a deterministic **work
//! counter**: one unit per slot or field read or written, counted identically
//! on both sides — instruction fetch, operand traffic, list walks, reference
//! counts, compaction passes. Wall clock is reported next to it as a
//! reality check, but the work counter is what the conclusions rest on.
//!
//! Space is the **peak live footprint**, sampled after every VM step:
//!
//! - flat: the tape, which holds the program and all data at once, plus the
//!   call-frame stack
//! - cons: live cells + the operand stack + the call-frame stack + the
//!   instruction array
//!
//! To put those in the same unit, both are converted to 8-byte words under a
//! stated model (see the constants below) rather than compared as raw slot
//! and cell counts.

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::time::Instant;

use super::cons;
use super::cons_emit;
use super::flat;
use super::flat_emit;
use super::lang::Program;

/// A flat tape slot: an op tag plus one payload. (The `mark` bit and the
/// `shift` scratch the compactor uses fit alongside the tag in a packed
/// encoding; the Rust struct is 40 bytes because nothing is packed.)
pub const FLAT_WORDS_PER_SLOT: usize = 2;
/// A cons cell: reference count, car, cdr.
pub const CONS_WORDS_PER_CELL: usize = 3;
/// A tagged value on the cons operand stack, and one bytecode instruction.
pub const CONS_WORDS_PER_SLOT: usize = 1;
/// A flat call frame (floor, base, args, return, deferred flag).
pub const FLAT_WORDS_PER_FRAME: usize = 5;
/// A cons call frame (base, return).
pub const CONS_WORDS_PER_FRAME: usize = 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Backend {
    /// The experiment: moves at last use, so the in-place paths can fire.
    Flat,
    /// The experiment with every operand borrowed: the copy-on-write cost
    /// model of the very same program.
    FlatShared,
    /// Cons cells, textbook persistent update (copy the spine, share the
    /// tail).
    ConsPersistent,
    /// Cons cells, reusing cells whose reference count is 1.
    ConsReuse,
}

impl Backend {
    pub fn label(self) -> &'static str {
        match self {
            Backend::Flat => "flat",
            Backend::FlatShared => "flat-shared",
            Backend::ConsPersistent => "cons",
            Backend::ConsReuse => "cons-reuse",
        }
    }

    pub fn is_flat(self) -> bool {
        matches!(self, Backend::Flat | Backend::FlatShared)
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Measure {
    pub answer: i64,
    pub reads: usize,
    pub writes: usize,
    pub steps: usize,
    pub allocs: usize,
    /// Peak flat tape length, in slots.
    pub peak_slots: usize,
    /// Peak live cons cells.
    pub peak_cells: usize,
    /// Peak cons operand stack, in slots.
    pub peak_stack: usize,
    /// Peak call-stack depth.
    pub peak_frames: usize,
    /// Program size: tape slots, or bytecode instructions.
    pub code: usize,
    /// Peak footprint in 8-byte words, program included.
    pub words: usize,
    pub nanos: u128,
}

impl Measure {
    pub fn work(&self) -> usize {
        self.reads + self.writes
    }
}

pub fn run(prog: &Program, backend: Backend, time: bool) -> Result<Measure, String> {
    match backend {
        Backend::Flat => run_flat(prog, true, time),
        Backend::FlatShared => run_flat(prog, false, time),
        Backend::ConsPersistent => run_cons(prog, false, time),
        Backend::ConsReuse => run_cons(prog, true, time),
    }
}

fn run_flat(prog: &Program, use_take: bool, time: bool) -> Result<Measure, String> {
    let code = flat_emit::compile(prog, use_take);
    let mut vm = flat::Vm::load(code.clone());
    let mut peak = vm.stack.len();
    let mut peak_frames = 0;
    let mut steps = 0;
    while vm.ip != vm.end {
        vm.eval_once(false)?;
        steps += 1;
        peak = peak.max(vm.stack.len());
        peak_frames = peak_frames.max(vm.frames.len());
    }
    vm.run(false)?; // ip == end, so this is the closing compaction alone
    peak = peak.max(vm.stack.len());
    let answer = match vm.stack.last().map(|s| s.op) {
        Some(flat::Op::Int(i)) => i,
        other => return Err(format!("expected an int result, got {other:?}")),
    };
    Ok(Measure {
        answer,
        reads: vm.stats.reads,
        writes: vm.stats.writes,
        steps,
        allocs: 0,
        peak_slots: peak,
        peak_cells: 0,
        peak_stack: 0,
        peak_frames,
        code: code.len(),
        words: peak * FLAT_WORDS_PER_SLOT + peak_frames * FLAT_WORDS_PER_FRAME,
        nanos: if time { time_flat(&code) } else { 0 },
    })
}

/// Where the flat VM's work goes, per kind of op: how often each one runs and
/// how many slot touches it costs. Answers "is this more instructions, or
/// more memory traffic per instruction, and which instruction".
pub fn profile_flat(prog: &Program) -> Result<Vec<(&'static str, usize, usize)>, String> {
    let code = flat_emit::compile(prog, true);
    let mut vm = flat::Vm::load(code);
    let mut by_op: BTreeMap<&'static str, (usize, usize)> = BTreeMap::new();
    while vm.ip != vm.end {
        // Read straight out of the Vec: going through the VM would count.
        let label = op_label(vm.stack[vm.ip].op);
        let before = vm.stats.reads + vm.stats.writes;
        vm.eval_once(false)?;
        let entry = by_op.entry(label).or_default();
        entry.0 += 1;
        entry.1 += vm.stats.reads + vm.stats.writes - before;
    }
    let before = vm.stats.reads + vm.stats.writes;
    vm.run(false)?;
    let entry = by_op.entry("(final compaction)").or_default();
    entry.0 += 1;
    entry.1 += vm.stats.reads + vm.stats.writes - before;
    let mut out: Vec<_> = by_op.into_iter().map(|(l, (n, w))| (l, n, w)).collect();
    out.sort_by_key(|(_, _, w)| std::cmp::Reverse(*w));
    Ok(out)
}

fn op_label(op: flat::Op) -> &'static str {
    use flat::{Op::*, SizedOp::*};
    match op {
        Moved => "moved",
        Int(_) => "int",
        Var { .. } => "var",
        Take { .. } => "take",
        Ref { .. } => "ref",
        Sized(BlobStart, _) => "blob",
        Sized(BlobEnd, _) => "blob-end",
        Sized(FnStart, _) => "fn-start",
        Sized(FnEnd { .. }, _) => "fn-end (return)",
        Sized(Call { .. }, _) => "call",
        Sized(List { .. }, _) => "list",
        Sized(Push { .. }, _) => "push",
        Sized(Pop { .. }, _) => "pop",
        Sized(Set, _) => "set",
        Sized(Get, _) => "get",
        Sized(If, _) => "if",
        Sized(Len, _) => "len",
        Sized(Bin(_), _) => "bin",
    }
}

fn run_cons(prog: &Program, fip: bool, time: bool) -> Result<Measure, String> {
    let code = cons_emit::compile(prog);
    let mut vm = cons::Vm::new(fip);
    let answer = match vm.run(&code.ins, code.entry)? {
        cons::CVal::Int(i) => i,
        other => return Err(format!("expected an int result, got {other:?}")),
    };
    let s = vm.stats;
    if s.live != 0 {
        return Err(format!("{} cells leaked", s.live));
    }
    Ok(Measure {
        answer,
        reads: s.reads,
        writes: s.writes,
        steps: s.steps,
        allocs: s.allocs,
        peak_slots: 0,
        peak_cells: s.peak_live,
        peak_stack: s.peak_stack,
        peak_frames: s.peak_frames,
        code: code.ins.len(),
        words: s.peak_live * CONS_WORDS_PER_CELL
            + (s.peak_stack + code.ins.len()) * CONS_WORDS_PER_SLOT
            + s.peak_frames * CONS_WORDS_PER_FRAME,
        nanos: if time { time_cons(&code, fip) } else { 0 },
    })
}

/// Wall clock: the fastest of a few runs, with setup outside the timer.
const TIME_BUDGET_NANOS: u128 = 30_000_000;
const MAX_REPS: usize = 25;

fn time_flat(code: &[flat::Op]) -> u128 {
    let mut best = u128::MAX;
    let mut total = 0;
    for _ in 0..MAX_REPS {
        let mut vm = flat::Vm::load(code.to_vec());
        let t = Instant::now();
        let r = vm.run(false);
        let ns = t.elapsed().as_nanos();
        assert!(r.is_ok());
        best = best.min(ns);
        total += ns;
        if total > TIME_BUDGET_NANOS {
            break;
        }
    }
    best
}

fn time_cons(code: &cons_emit::Code, fip: bool) -> u128 {
    let mut best = u128::MAX;
    let mut total = 0;
    for _ in 0..MAX_REPS {
        let mut vm = cons::Vm::new(fip);
        let t = Instant::now();
        let r = vm.run(&code.ins, code.entry);
        let ns = t.elapsed().as_nanos();
        assert!(r.is_ok());
        best = best.min(ns);
        total += ns;
        if total > TIME_BUDGET_NANOS {
            break;
        }
    }
    best
}
