//! Guards for the benchmark in `benches/comparison.rs`.
//!
//! A benchmark is only worth reading if the programs it compares compute the
//! same thing and if the compiler feeding each VM is not quietly handicapping
//! one of them. These tests pin both, plus the asymptotic claims the write-up
//! makes, so a change to the VM that breaks one of them fails loudly.

#[path = "../benches/harness/mod.rs"]
mod harness;

use harness::lang::Program;
use harness::run::{Backend, profile_flat, run};
use harness::tasks::{backends_for, suite};

fn work(prog: &Program, backend: Backend) -> usize {
    run(prog, backend, false).expect("program runs").work()
}

/// Work per element at n, then at 4n: ~1.0 is linear, ~4.0 is quadratic.
fn growth(build: fn(usize) -> Program, backend: Backend, n: usize) -> f64 {
    let small = work(&build(n), backend) as f64 / n as f64;
    let large = work(&build(4 * n), backend) as f64 / (4 * n) as f64;
    large / small
}

fn variant(task: &str, idiom: &str) -> fn(usize) -> Program {
    let t = suite().into_iter().find(|t| t.name == task).expect("task");
    t.variants.iter().find(|v| v.idiom == idiom).expect("variant").build
}

fn assert_linear(task: &str, idiom: &str, backend: Backend, n: usize) {
    let g = growth(variant(task, idiom), backend, n);
    assert!(g < 1.4, "{task}/{idiom} on {}: work per element grew {g:.1}x", backend.label());
}

/// A pure quadratic term gives 4.0; a quadratic phase mixed with a linear
/// one (a walk-built list read at random, say) gives less, so the bar for
/// "clearly super-linear" is 2.0.
fn assert_quadratic(task: &str, idiom: &str, backend: Backend, n: usize) {
    let g = growth(variant(task, idiom), backend, n);
    assert!(g > 2.0, "{task}/{idiom} on {}: work per element grew only {g:.1}x", backend.label());
}

// --- the programs mean the same thing on every backend ---------------------

#[test]
fn every_backend_agrees_on_every_task() {
    for task in suite() {
        let n = task.sizes[0];
        let mut expected: Option<(i64, String)> = None;
        for v in &task.variants {
            let prog = (v.build)(n);
            for backend in backends_for(&prog) {
                let m = run(&prog, backend, false).unwrap_or_else(|e| {
                    panic!("{}/{} on {}: {e}", task.name, v.idiom, backend.label())
                });
                let who = format!("{}/{} on {}", task.name, v.idiom, backend.label());
                match &expected {
                    None => expected = Some((m.answer, who)),
                    Some((want, first)) => {
                        assert_eq!(m.answer, *want, "{who} disagrees with {first}");
                    }
                }
            }
        }
        assert!(expected.is_some(), "{} ran nowhere", task.name);
    }
}

// --- the flat backend is not handicapped -----------------------------------

#[test]
fn the_compiler_matches_the_hand_written_tape() {
    // The same in-place index map as `increment_map` in tests/vm.rs, entered
    // the same way. If the compiler ever emits something the VM's own tests
    // would not, the work counters diverge and this fails.
    use harness::flat::{BinOp, Op::*, SizedOp, SizedOp::*};
    use harness::lang::*;

    let n = 500;
    let mut hand = vec![
        Sized(FnStart, 25), // fn(self, l, i)
        Sized(FnStart, 1),  // then: l
        Var { elem: 1 },
        Sized(FnEnd { args: 0 }, 1),
        Sized(FnStart, 15), // else
        Var { elem: 0 },    // [self, self]
        Var { elem: 0 },
        Sized(SizedOp::List { elems: 2 }, 0),
        Take { elem: 1 }, // set(take l, get(l, i) + 1, i)
        Var { elem: 1 },
        Var { elem: 2 },
        Sized(Get, 0),
        Int(1),
        Sized(Bin(BinOp::Add), 0),
        Var { elem: 2 },
        Sized(Set, 0),
        Var { elem: 2 }, // i + 1
        Int(1),
        Sized(Bin(BinOp::Add), 0),
        Sized(Call { args: 2, comptime: false }, 0), // tail call
        Sized(FnEnd { args: 0 }, 15),
        Var { elem: 1 }, // cond: len(l) == i
        Sized(Len, 0),
        Var { elem: 2 },
        Sized(Bin(BinOp::Eq), 0),
        Sized(If, 0),
        Sized(FnEnd { args: 3 }, 25),
        Ref { offset: 1 },
        Ref { offset: 2 },
        Sized(SizedOp::List { elems: 2 }, 0),
    ];
    hand.extend((0..n).map(|i| Int(i as i64)));
    hand.push(Sized(SizedOp::List { elems: n }, 0));
    hand.push(Int(0));
    hand.push(Sized(Call { args: 2, comptime: false }, 0));
    hand.push(Sized(Len, 0));

    let items: Vec<Expr> = (0..n).map(|i| int(i as i64)).collect();
    let compiled = Program {
        funcs: vec![rec(
            "map",
            vec!["l", "i"],
            iff(
                eq(len(var("l")), var("i")),
                var("l"),
                call(
                    "map",
                    vec![
                        set(var("l"), add(get(var("l"), var("i")), int(1)), var("i")),
                        add(var("i"), int(1)),
                    ],
                ),
            ),
        )],
        main: len(call("map", vec![list(items), int(0)])),
    };
    let compiled = harness::flat_emit::compile(&compiled, true);

    let mut a = harness::flat::Vm::load(hand);
    a.run(false).expect("hand-written");
    let mut b = harness::flat::Vm::load(compiled);
    b.run(false).expect("compiled");
    assert_eq!(
        (a.stats.reads, a.stats.writes),
        (b.stats.reads, b.stats.writes),
        "the compiled tape does different work than the hand-written one"
    );
}

// --- what the flat model wins ----------------------------------------------

#[test]
fn indexed_update_is_linear_on_the_tape_and_quadratic_on_cons() {
    assert_linear("map", "index", Backend::Flat, 256);
    assert_quadratic("map", "index", Backend::ConsPersistent, 256);
    // Reuse removes the allocation but not the walk to the element.
    assert_quadratic("map", "index", Backend::ConsReuse, 256);
}

#[test]
fn random_access_is_flat_and_linear_only_on_the_tape() {
    assert_linear("random_access", "index", Backend::Flat, 256);
    assert_quadratic("random_access", "index", Backend::ConsReuse, 256);
    // Building the list the cons way does not help: the reads still walk.
    assert_quadratic("random_access", "walk", Backend::ConsReuse, 256);
}

#[test]
fn growing_and_draining_at_the_end_is_linear_on_the_tape() {
    assert_linear("build", "index", Backend::Flat, 256);
    assert_linear("drain", "index", Backend::Flat, 256);
    assert_quadratic("build", "index", Backend::ConsReuse, 256);
    assert_quadratic("drain", "index", Backend::ConsReuse, 256);
}

#[test]
fn the_tape_allocates_nothing() {
    for task in suite() {
        let n = task.sizes[0];
        for v in &task.variants {
            let prog = (v.build)(n);
            if !prog.runs_on_flat() {
                continue;
            }
            let m = run(&prog, Backend::Flat, false).expect("runs");
            assert_eq!(m.allocs, 0, "{}/{}", task.name, v.idiom);
        }
    }
}

#[test]
fn the_tape_does_not_retain_what_it_discharged() {
    // The discharge's slide reclaims everything above the highest referenced
    // target, which is most of the junk and costs O(block). What it cannot
    // reach is data orphaned *below* that target — a copy-path original, a
    // tombstoned inner list — and collecting those is the whole job of the
    // full compaction. Nothing else in this file would notice if it stopped
    // running, because every other asymptotic test measures work, and
    // retention is a space property: skipping the compaction makes a program
    // *cheaper* and leaves the garbage on the tape.
    //
    // `garbage` orphans a four-element temporary per element. Measured peak,
    // in words per element: 15.3 at n=512 and 15.1 at n=2048 with the
    // compaction running, 36.3 and 36.1 with it disabled.
    for n in [512, 2048] {
        let prog = variant("garbage", "index")(n);
        let m = run(&prog, Backend::Flat, false).expect("runs");
        let per = m.words as f64 / n as f64;
        assert!(per < 22.0, "garbage n={n}: peak is {per:.1} words per element");
    }
}

// --- what the flat model loses ---------------------------------------------

#[test]
fn moves_are_what_makes_it_linear() {
    // The same program with every operand borrowed is the copy-on-write cost
    // model: the in-place paths cannot fire and the loop is quadratic.
    assert_quadratic("map", "index", Backend::FlatShared, 256);
    assert_quadratic("build", "index", Backend::FlatShared, 256);
}

#[test]
fn a_shared_list_costs_a_full_copy_per_version() {
    // Forking one list many times is where structural sharing pays: cons
    // shares the tail after the changed element, the tape has to copy.
    assert_quadratic("fork_head", "index", Backend::Flat, 256);
    assert_linear("fork_head", "walk", Backend::ConsPersistent, 256);
    // ... but only when the change is near the front. At the far end cons
    // copies the whole spine too.
    assert_quadratic("fork_last", "walk", Backend::ConsPersistent, 256);
}

#[test]
fn pushing_a_freshly_built_element_cannot_stay_in_place() {
    // A tape reference always points backwards, so a list may not adopt an
    // element younger than itself: `push(l, list(i, i * 2))` copies the list
    // every time and building a list of records is quadratic.
    assert_quadratic("nested", "index", Backend::Flat, 256);
    // The same push with an element that is older than the list stays in
    // place, which isolates the rule above as the cause.
    assert_linear("nested_shared", "index", Backend::Flat, 256);
    // Cons has no such rule: the walk idiom builds records in linear time.
    assert_linear("nested", "walk", Backend::ConsPersistent, 256);
}

#[test]
fn the_cons_walk_idiom_is_linear_where_the_tape_has_no_answer() {
    for (task, idiom) in
        [("build", "walk"), ("map", "walk"), ("reverse", "walk"), ("drain", "walk")]
    {
        assert_linear(task, idiom, Backend::ConsPersistent, 256);
        assert_linear(task, idiom, Backend::ConsReuse, 256);
    }
}

// --- cons cells hosted on the tape -----------------------------------------

#[test]
fn a_cons_cell_costs_the_tape_a_constant() {
    // A cons cell is a two-element list `[head, tail]`, which needs no new
    // primitive, and its tail is always older than the cell pointing at it —
    // so the backwards-only reference rule that makes `nested` quadratic is
    // satisfied by construction. Building one and reading either field are
    // both O(1) and cheap; if that were not so, hosting linked structures on
    // the tape would be off the table.
    // `nested` is the sharper case: each cell adopts a pair built moments
    // earlier, which is exactly what a flat list cannot do.
    for task in ["build", "nested"] {
        let prog = variant(task, "pairs")(1024);
        let rows = profile_flat(&prog).expect("runs");
        for op in ["list", "get"] {
            let (_, count, work) = rows.iter().find(|(l, _, _)| *l == op).expect("op ran");
            let per = *work as f64 / *count as f64;
            assert!(per < 20.0, "{task}: {op} costs {per:.1} work units per execution");
        }
    }
}

#[test]
fn the_cons_vm_runs_the_emulated_cells_linearly() {
    // Two cells per logical cell, so it is a handicap — but only a constant
    // one. The program itself is fine.
    assert_linear("build", "pairs", Backend::ConsPersistent, 256);
    assert_linear("map", "pairs", Backend::ConsPersistent, 256);
    assert_linear("nested", "pairs", Backend::ConsPersistent, 256);
}

#[test]
fn cons_cells_on_the_tape_are_linear() {
    // So the tape hosts a linked structure as well as a flat one: O(1)
    // structural sharing (`fork_head`) and a linear way to build a list of
    // fresh records (`nested`), neither of which a flat extent can do, and
    // both with no heap.
    //
    // This needed the discharge to stop deciding by liveness estimate. The
    // old `max_live - from > 2 * sum_live` measured a referenced value by its
    // own extent — exact for a contiguous list, short by a factor of n for a
    // chain — so a full mark-and-compact ran over the whole chain on every
    // tail call, ~98% of the program's work at n=1024.
    assert_linear("build", "pairs", Backend::Flat, 256);
    assert_linear("fork_head", "pairs", Backend::Flat, 256);
    assert_linear("nested", "pairs", Backend::Flat, 256);
}

#[test]
fn the_tail_call_discharge_is_constant_per_iteration() {
    // The sharper form of the test above, and the one that fails first if the
    // discharge ever goes back to compacting on a schedule it cannot afford:
    // the cost of a single `call` must not grow with the size of the live
    // region it is discharging. A chain is the hard case, because the whole
    // region is live and a compaction that runs over it recovers nothing.
    for (task, idiom) in [("build", "pairs"), ("nested", "pairs"), ("build", "index")] {
        let small = call_cost(task, idiom, 256);
        let large = call_cost(task, idiom, 1024);
        assert!(
            large / small < 1.4,
            "{task}/{idiom}: work per call grew {:.1}x ({small:.0} -> {large:.0}) for 4x the elements",
            large / small
        );
    }
}

/// Work per executed `call` op, from the flat VM's per-op profile.
fn call_cost(task: &str, idiom: &str, n: usize) -> f64 {
    let prog = variant(task, idiom)(n);
    let rows = profile_flat(&prog).expect("runs");
    let (_, count, work) = rows.iter().find(|(l, _, _)| *l == "call").expect("calls ran");
    *work as f64 / *count as f64
}

// --- the interpreter floor -------------------------------------------------

#[test]
fn a_loop_with_no_lists_already_costs_the_tape_more() {
    // Every list result has to be read against this: a bare tail-recursive
    // loop, no data structures at all. The tape pays for a closure and two
    // branch thunks per iteration, and for scanning its own frame.
    let f = variant("loop", "-");
    let flat = work(&f(4096), Backend::Flat) as f64;
    let cons = work(&f(4096), Backend::ConsPersistent) as f64;
    assert!(flat / cons > 2.0, "expected the tape to cost more per iteration, got {flat}/{cons}");
    assert!(flat / cons < 6.0, "the gap has grown: {flat}/{cons}");
}
