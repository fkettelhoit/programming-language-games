//! The experiment's VM.
//!
//! `Vm::eval_once` is public, so the harness can single-step and sample peak
//! stack occupancy after every op; `Vm::run` with `ip == end` performs only
//! the closing compaction, which is how a stepped run is finished.

pub use flat_stack_mutation::*;
