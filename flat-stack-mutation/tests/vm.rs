use Op::*;
use SizedOp::*;
use flat_stack_mutation::{BinOp, Op, SizedOp, Vm};

fn run(program: Vec<Op>, comptime: bool) -> Vec<Op> {
    let mut vm = Vm::load(program);
    if let Err(e) = vm.run(comptime) {
        panic!("VM error: {e}\n{vm:#?}");
    }
    vm.stack.into_iter().map(|slot| slot.op).collect()
}

fn run_err(program: Vec<Op>, comptime: bool) -> &'static str {
    let mut vm = Vm::load(program);
    match vm.run(comptime) {
        Ok(()) => {
            let tape: Vec<Op> = vm.stack.into_iter().map(|slot| slot.op).collect();
            panic!("expected an error, got tape {tape:?}");
        }
        Err(e) => e,
    }
}

/// Reload `tape` as the next stage's program, call its topmost value with the
/// given int args at runtime, and return the full resulting tape.
fn reload_and_call(tape: Vec<Op>, args: &[i64]) -> Vec<Op> {
    let ops: Vec<Vec<Op>> = args.iter().map(|&a| vec![Int(a)]).collect();
    reload_and_call_with(tape, &ops)
}

/// Like `reload_and_call`, but each argument is an arbitrary op sequence.
fn reload_and_call_with(tape: Vec<Op>, args: &[Vec<Op>]) -> Vec<Op> {
    let mut prog = tape;
    let f_end = prog.len() - 1;
    prog.push(Ref { offset: prog.len() - f_end });
    for arg in args {
        prog.extend_from_slice(arg);
    }
    prog.push(Sized(Call { args: args.len(), comptime: false }, 0));
    run(prog, false)
}

/// `g = fn() 5` — the comptime-applied function used to trigger symbolic walks.
fn g() -> Vec<Op> {
    vec![Sized(FnStart, 1), Int(5), Sized(FnEnd { args: 0 }, 1)]
}

// --- pop: copy path ------------------------------------------------------------

#[test]
fn pop_of_physical_list_yields_canonical_pair() {
    // pop{1} on [1, 2, 3] leaves a single value: the pair [rest, elem]. The
    // pair follows the same normalization convention as every other
    // list-producing op — its element region is packed, one slot per element,
    // so element 0 is a handle to rest, not the rest header itself. That is
    // what makes the pair a value at comptime (is_value's packed check), lets
    // Get's physical path address elements by slot, and lets compaction mark
    // the elements precisely: the consumed original [1, 2, 3] is collected
    // here because its atoms were copied out and nothing references it.
    assert_eq!(
        run(
            vec![Int(1), Int(2), Int(3), Sized(List { elems: 3 }, 0), Sized(Pop { elems: 1 }, 0)],
            false
        ),
        [
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 2), // rest = [1, 2]
            Ref { offset: 1 },           // pair element 0 -> rest
            Int(3),                      // pair element 1 = the popped atom
            Sized(List { elems: 2 }, 5), // the pair, extending to its base
        ]
    );
}

#[test]
fn popped_element_is_the_last() {
    // get(pop1([1, 2, 3]), 1) == 3 — in the flat layout the cheap end is the
    // back, so pop takes the topmost element.
    let tape = run(
        vec![
            Int(1),
            Int(2),
            Int(3),
            Sized(List { elems: 3 }, 0),
            Sized(Pop { elems: 1 }, 0),
            Int(1),
            Sized(Get, 0),
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(3)));
}

#[test]
fn popped_rest_keeps_its_elements() {
    // get(get(pop1([1, 2, 3]), 0), 1) == 2 — extracting rest goes through the
    // pair's element-0 handle (an internal ref, resolved by Get's compacting
    // arm), and the shortened list still indexes correctly.
    let tape = run(
        vec![
            Int(1),
            Int(2),
            Int(3),
            Sized(List { elems: 3 }, 0),
            Sized(Pop { elems: 1 }, 0),
            Int(0),
            Sized(Get, 0),
            Int(1),
            Sized(Get, 0),
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(2)));
}

#[test]
fn pop_of_several_elements_keeps_their_order() {
    // pop{2} on [1, 2, 3] yields [rest, 2, 3]: popped elements appear in
    // original order, so Pop{k} is the exact inverse of Push{k}.
    let tape = run(
        vec![
            Int(1),
            Int(2),
            Int(3),
            Sized(List { elems: 3 }, 0),
            Sized(Pop { elems: 2 }, 0),
            Int(1),
            Sized(Get, 0),
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(2)));
}

#[test]
fn pop_of_all_elements_leaves_empty_rest() {
    // pop{3} on [1, 2, 3] yields [[], 1, 2, 3]; extracting rest gives the
    // empty list, and the closing compaction collects everything else.
    assert_eq!(
        run(
            vec![
                Int(1),
                Int(2),
                Int(3),
                Sized(List { elems: 3 }, 0),
                Sized(Pop { elems: 3 }, 0),
                Int(0),
                Sized(Get, 0),
            ],
            false,
        ),
        [Sized(List { elems: 0 }, 0)]
    );
}

#[test]
fn fully_drained_pop_stores_empty_rest_in_place() {
    // The empty list is the one Sized value that is atom-like: one slot,
    // self-contained. A fully drained pop therefore stores the empty rest
    // header DIRECTLY in the pair's element-0 slot — no handle — exactly as
    // List construction leaves any 1-slot element in place. This pins the
    // layout itself (the ref version would leave a 4-slot tape); the in-place
    // pop of stage 5 must reproduce this same shape.
    assert_eq!(
        run(vec![Int(1), Sized(List { elems: 1 }, 0), Sized(Pop { elems: 1 }, 0)], false),
        [
            Sized(List { elems: 0 }, 0), // pair element 0: empty rest, in place
            Int(1),                      // pair element 1: the popped atom
            Sized(List { elems: 2 }, 2),
        ]
    );
}

#[test]
fn borrowed_empty_list_is_copied_not_referenced() {
    // borrow treats the empty list as an atom too: copying a list whose
    // element region holds a physical empty header must copy it, not ref it.
    // push([[], 1], 2) — with a copying borrow the new list carries no refs,
    // so the consumed original is fully collected; a ref-borrow would pin the
    // old extent alive and the tape would retain it as garbage.
    assert_eq!(
        run(
            vec![
                Sized(List { elems: 0 }, 0), // []
                Int(1),
                Sized(List { elems: 2 }, 0), // l = [[], 1]
                Int(2),
                Sized(Push { elems: 1 }, 0), // push(l, 2)
            ],
            false
        ),
        [
            Sized(List { elems: 0 }, 0),
            Int(1),
            Int(2),
            Sized(List { elems: 3 }, 3),
        ]
    );
}

#[test]
fn pop_of_zero_elements_wraps_the_whole_list() {
    // pop{0} is degenerate but well-defined: the pair is [rest] with rest the
    // untouched list. len(get(pop0([1, 2]), 0)) == 2.
    let tape = run(
        vec![
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 0),
            Sized(Pop { elems: 0 }, 0),
            Int(0),
            Sized(Get, 0),
            Sized(Len, 0),
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(2)));
}

#[test]
fn pop_of_more_than_len_errors() {
    let err = run_err(
        vec![Int(1), Sized(List { elems: 1 }, 0), Sized(Pop { elems: 2 }, 0)],
        false,
    );
    assert_eq!(err, "List index is out of bounds");
}

#[test]
fn pop_of_non_list_errors() {
    assert_eq!(run_err(vec![Int(1), Sized(Pop { elems: 1 }, 0)], false), "Invalid list");
}

#[test]
fn pop_through_a_borrowed_arg() {
    // f(x) = get(pop1(x), 1), f([1, 2, 3]) == 3 — the via-ref path: inside f
    // the list is only reachable through the arg slot's borrow, and the pair
    // extends over the ref operand rather than the (unowned) original.
    let tape = run(
        vec![
            Sized(FnStart, 4),                           // 0  f
            Var { elem: 0 },                             // 1
            Sized(Pop { elems: 1 }, 0),                  // 2
            Int(1),                                      // 3
            Sized(Get, 0),                               // 4
            Sized(FnEnd { args: 1 }, 4),                 // 5
            Ref { offset: 1 },                           // 6  -> f
            Int(1),                                      // 7
            Int(2),                                      // 8
            Int(3),                                      // 9
            Sized(List { elems: 3 }, 0),                 // 10
            Sized(Call { args: 1, comptime: false }, 0), // 11
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(3)));
}

#[test]
fn pop_of_list_with_nested_last_element() {
    // l = [1, [2, 3]]: the popped element is a ref into the pair's adopted
    // extent; extracting it must keep the nested list alive through
    // compaction. get(get(pop1(l), 1), 0) == 2.
    let tape = run(
        vec![
            Int(1),
            Int(2),
            Int(3),
            Sized(List { elems: 2 }, 0), // inner = [2, 3]
            Sized(List { elems: 2 }, 0), // l = [1, inner]
            Sized(Pop { elems: 1 }, 0),
            Int(1),
            Sized(Get, 0),
            Int(0),
            Sized(Get, 0),
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(2)));
}

#[test]
fn pop_destructured_through_a_call_reassembles() {
    // f(p) = push(get(p, 0), get(p, 1)) — the "bind is a call" pattern from
    // the design discussion: both pair halves are consumed via Var borrows,
    // and push(rest, elem) rebuilds the original list. get(f(pop1(l)), 2) == 3.
    let tape = run(
        vec![
            Sized(FnStart, 7),                           // 0  f
            Var { elem: 0 },                             // 1
            Int(0),                                      // 2
            Sized(Get, 0),                               // 3
            Var { elem: 0 },                             // 4
            Int(1),                                      // 5
            Sized(Get, 0),                               // 6
            Sized(Push { elems: 1 }, 0),                 // 7
            Sized(FnEnd { args: 1 }, 7),                 // 8
            Ref { offset: 1 },                           // 9  -> f
            Int(1),                                      // 10
            Int(2),                                      // 11
            Int(3),                                      // 12
            Sized(List { elems: 3 }, 0),                 // 13
            Sized(Pop { elems: 1 }, 0),                  // 14
            Sized(Call { args: 1, comptime: false }, 0), // 15
            Int(2),                                      // 16
            Sized(Get, 0),                               // 17
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(3)));
}

// --- pop: comptime -------------------------------------------------------------

#[test]
fn comptime_pop_with_resolved_list_evaluates() {
    // f(xs) = get(pop1(xs), 1), called as f!([1, 2]) — a resolved operand
    // means Pop and Get both evaluate at comptime, which requires the pair to
    // count as a value (packed element region). Regression guard: an
    // unnormalized pair fails is_value, so the Get would spuriously defer and
    // the tape would end in a residual span instead of 2.
    let prog = vec![
        Sized(FnStart, 4),                          // 0  f
        Var { elem: 0 },                            // 1
        Sized(Pop { elems: 1 }, 0),                 // 2
        Int(1),                                     // 3
        Sized(Get, 0),                              // 4
        Sized(FnEnd { args: 1 }, 4),                // 5
        Ref { offset: 1 },                          // 6  -> f
        Int(1),                                     // 7
        Int(2),                                     // 8
        Sized(List { elems: 2 }, 0),                // 9
        Sized(Call { args: 1, comptime: true }, 0), // 10
    ];
    assert_eq!(run(prog, true).last(), Some(&Int(2)));
}

#[test]
fn deferred_pop_round_trips() {
    // f(x) = get(pop1(x), 1) with x unresolved: Pop defers on the var, Get
    // defers on the Pop span (computations are contagious), and the residual
    // program computes the same result as direct evaluation — the
    // stage-uniformity property that made single-valued Pop the design choice.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 6),                          // 3  f
        Ref { offset: 2 },                          // 4  -> g
        Sized(Call { args: 0, comptime: true }, 0), // 5
        Var { elem: 0 },                            // 6
        Sized(Pop { elems: 1 }, 0),                 // 7
        Int(1),                                     // 8
        Sized(Get, 0),                              // 9
        Sized(FnEnd { args: 1 }, 6),                // 10
    ]);
    let stage1 = run(prog, true);
    assert!(
        stage1.iter().any(|op| matches!(op, Sized(Pop { .. }, _))),
        "expected a residual Pop span, got {stage1:?}"
    );
    let tape = reload_and_call_with(stage1, &[vec![Int(8), Int(9), Sized(List { elems: 2 }, 0)]]);
    assert_eq!(tape.last(), Some(&Int(9)));
}

// --- tail calls ----------------------------------------------------------------

#[test]
fn plain_tail_call_discharges_the_caller_frame() {
    // f(x) = h(x) with the call in tail position: the caller's frame region is
    // discharged before the jump, and h returns straight to f's caller.
    // f(21) == 42.
    let tape = run(
        vec![
            Sized(FnStart, 3),                           // 0  h = fn(a) a * 2
            Var { elem: 0 },                             // 1
            Int(2),                                      // 2
            Sized(Bin(BinOp::Mul), 0),                   // 3
            Sized(FnEnd { args: 1 }, 3),                 // 4
            Sized(FnStart, 3),                           // 5  f = fn(x) h(x)
            Ref { offset: 2 },                           // 6  -> h
            Var { elem: 0 },                             // 7
            Sized(Call { args: 1, comptime: false }, 0), // 8
            Sized(FnEnd { args: 1 }, 3),                 // 9
            Ref { offset: 1 },                           // 10 -> f
            Int(21),                                     // 11
            Sized(Call { args: 1, comptime: false }, 0), // 12
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(42)));
}

#[test]
fn tail_call_with_empty_list_arg_keeps_it_intact() {
    // f(x) = h(x, []) in tail position — after the discharge, the topmost
    // surviving slot is the empty-list arg. The block discharge must not run
    // gc_until's closing extent fixup, which would rewrite that header's
    // slots into a bogus region-sized extent. h(a, b) = len(b) == 0.
    let tape = run(
        vec![
            Sized(FnStart, 2),                           // 0  h = fn(a, b) len(b)
            Var { elem: 1 },                             // 1
            Sized(Len, 0),                               // 2
            Sized(FnEnd { args: 2 }, 2),                 // 3
            Sized(FnStart, 4),                           // 4  f = fn(x) h(x, [])
            Ref { offset: 2 },                           // 5  -> h
            Var { elem: 0 },                             // 6
            Sized(List { elems: 0 }, 0),                 // 7
            Sized(Call { args: 2, comptime: false }, 0), // 8
            Sized(FnEnd { args: 1 }, 4),                 // 9
            Ref { offset: 1 },                           // 10 -> f
            Int(7),                                      // 11
            Sized(Call { args: 1, comptime: false }, 0), // 12
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(0)));
}

/// f(x, c) = if c { h(x) } else { x } with h = fn(a) a * 2, called as f(21, c).
fn tail_call_in_branch(c: i64) -> Vec<Op> {
    vec![
        Sized(FnStart, 3),                           // 0  h
        Var { elem: 0 },                             // 1
        Int(2),                                      // 2
        Sized(Bin(BinOp::Mul), 0),                   // 3
        Sized(FnEnd { args: 1 }, 3),                 // 4
        Sized(FnStart, 10),                          // 5  f
        Sized(FnStart, 3),                           // 6  then: h(x)
        Ref { offset: 3 },                           // 7  -> h
        Var { elem: 0 },                             // 8
        Sized(Call { args: 1, comptime: false }, 0), // 9
        Sized(FnEnd { args: 0 }, 3),                 // 10
        Sized(FnStart, 1),                           // 11 else: x
        Var { elem: 0 },                             // 12
        Sized(FnEnd { args: 0 }, 1),                 // 13
        Var { elem: 1 },                             // 14
        Sized(If, 0),                                // 15
        Sized(FnEnd { args: 2 }, 10),                // 16
        Ref { offset: 1 },                           // 17 -> f
        Int(21),                                     // 18
        Int(c),                                      // 19
        Sized(Call { args: 2, comptime: false }, 0), // 20
    ]
}

#[test]
fn tail_call_in_branch_collapses_the_frame_chain() {
    // The call in the then-arm is followed by the branch thunk's FnEnd, whose
    // join is f's own FnEnd: the collapse must retire both the If frame and
    // f's frame, and h returns straight to f's caller.
    assert_eq!(run(tail_call_in_branch(1), false).last(), Some(&Int(42)));
}

#[test]
fn untaken_tail_branch_still_returns_plainly() {
    assert_eq!(run(tail_call_in_branch(0), false).last(), Some(&Int(21)));
}

/// countdown as a self-capturing closure: c = [code, code]; c(n).
fn countdown(n: i64) -> Vec<Op> {
    vec![
        Sized(FnStart, 16),                          // 0  fn(self, n)
        Sized(FnStart, 1),                           // 1  then
        Int(0),                                      // 2
        Sized(FnEnd { args: 0 }, 1),                 // 3
        Sized(FnStart, 7),                           // 4  else: self([self, self], n - 1)
        Var { elem: 0 },                             // 5
        Var { elem: 0 },                             // 6
        Sized(List { elems: 2 }, 0),                 // 7
        Var { elem: 1 },                             // 8
        Int(1),                                      // 9
        Sized(Bin(BinOp::Sub), 0),                   // 10
        Sized(Call { args: 1, comptime: false }, 0), // 11
        Sized(FnEnd { args: 0 }, 7),                 // 12
        Var { elem: 1 },                             // 13
        Int(0),                                      // 14
        Sized(Bin(BinOp::Eq), 0),                    // 15
        Sized(If, 0),                                // 16
        Sized(FnEnd { args: 2 }, 16),                // 17
        Ref { offset: 1 },                           // 18
        Ref { offset: 2 },                           // 19
        Sized(List { elems: 2 }, 0),                 // 20
        Int(n),                                      // 21
        Sized(Call { args: 1, comptime: false }, 0), // 22
    ]
}

#[test]
fn deep_tail_recursion_runs_in_constant_space() {
    // The acceptance test for TCO: the recursive call goes through the
    // closure arm (self-recursion is always closure-arm recursion here), and
    // each iteration collapses the If frame plus the function frame and
    // discharges the dying region. Vec::truncate never shrinks capacity, so
    // the post-run capacities are peak watermarks: without the collapse this
    // run needs ~8×10^4 stack slots and 2×10^4 frames.
    let mut vm = Vm::load(countdown(10_000));
    vm.run(false).expect("countdown(10_000)");
    assert_eq!(vm.stack.last().map(|slot| slot.op), Some(Int(0)));
    assert!(vm.stack.capacity() < 4096, "stack peaked at {}", vm.stack.capacity());
    assert!(vm.frames.capacity() < 64, "frames peaked at {}", vm.frames.capacity());
}

#[test]
fn tail_recursive_sum_accumulates() {
    // sum(n, acc) = if n == 0 { acc } else { sum(n - 1, acc + n) } — the
    // accumulator flows through the collapsed frames; sum(10_000) checks
    // that per-iteration discharge keeps exactly the live args.
    let tape = run(
        vec![
            Sized(FnStart, 19),                          // 0  fn(self, n, acc)
            Sized(FnStart, 1),                           // 1  then
            Var { elem: 2 },                             // 2
            Sized(FnEnd { args: 0 }, 1),                 // 3
            Sized(FnStart, 10),                          // 4  else
            Var { elem: 0 },                             // 5
            Var { elem: 0 },                             // 6
            Sized(List { elems: 2 }, 0),                 // 7
            Var { elem: 1 },                             // 8
            Int(1),                                      // 9
            Sized(Bin(BinOp::Sub), 0),                   // 10
            Var { elem: 2 },                             // 11
            Var { elem: 1 },                             // 12
            Sized(Bin(BinOp::Add), 0),                   // 13
            Sized(Call { args: 2, comptime: false }, 0), // 14
            Sized(FnEnd { args: 0 }, 10),                // 15
            Var { elem: 1 },                             // 16
            Int(0),                                      // 17
            Sized(Bin(BinOp::Eq), 0),                    // 18
            Sized(If, 0),                                // 19
            Sized(FnEnd { args: 3 }, 19),                // 20
            Ref { offset: 1 },                           // 21
            Ref { offset: 2 },                           // 22
            Sized(List { elems: 2 }, 0),                 // 23
            Int(10_000),                                 // 24
            Int(0),                                      // 25
            Sized(Call { args: 2, comptime: false }, 0), // 26
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(50_005_000)));
}

/// loop(l, i) = if i == 0 { l } else { loop(push(l, i), i - 1) }, then `tail`.
fn list_accumulator(n: i64, tail: &[Op]) -> Vec<Op> {
    let mut prog = vec![
        Sized(FnStart, 19),                          // 0  fn(self, l, i)
        Sized(FnStart, 1),                           // 1  then
        Var { elem: 1 },                             // 2
        Sized(FnEnd { args: 0 }, 1),                 // 3
        Sized(FnStart, 10),                          // 4  else
        Var { elem: 0 },                             // 5
        Var { elem: 0 },                             // 6
        Sized(List { elems: 2 }, 0),                 // 7
        Var { elem: 1 },                             // 8
        Var { elem: 2 },                             // 9
        Sized(Push { elems: 1 }, 0),                 // 10
        Var { elem: 2 },                             // 11
        Int(1),                                      // 12
        Sized(Bin(BinOp::Sub), 0),                   // 13
        Sized(Call { args: 2, comptime: false }, 0), // 14
        Sized(FnEnd { args: 0 }, 10),                // 15
        Var { elem: 2 },                             // 16
        Int(0),                                      // 17
        Sized(Bin(BinOp::Eq), 0),                    // 18
        Sized(If, 0),                                // 19
        Sized(FnEnd { args: 3 }, 19),                // 20
        Ref { offset: 1 },                           // 21
        Ref { offset: 2 },                           // 22
        Sized(List { elems: 2 }, 0),                 // 23
        Sized(List { elems: 0 }, 0),                 // 24
        Int(n),                                      // 25
        Sized(Call { args: 2, comptime: false }, 0), // 26
    ];
    prog.extend_from_slice(tail);
    prog
}

#[test]
fn tail_recursive_list_accumulator_stays_linear() {
    // Each iteration's copy-path push builds a fresh list in the dying frame;
    // the outgoing arg borrows it, so the discharge must keep the new copy
    // and drop the previous one. Peak stack is O(list), not O(iterations ×
    // list) — the watermark distinguishes ~2.5k slots from ~500k.
    let mut vm = Vm::load(list_accumulator(1000, &[Sized(Len, 0)]));
    vm.run(false).expect("accumulator(1000)");
    assert_eq!(vm.stack.last().map(|slot| slot.op), Some(Int(1000)));
    assert!(vm.stack.capacity() < 16384, "stack peaked at {}", vm.stack.capacity());
}

#[test]
fn list_accumulator_builds_in_push_order() {
    // loop([], 3) == [3, 2, 1]: i counts down while push appends.
    let tape = run(list_accumulator(3, &[Int(0), Sized(Get, 0)]), false);
    assert_eq!(tape.last(), Some(&Int(3)));
}

#[test]
fn tail_call_through_nested_ifs_collapses_the_chain() {
    // f(x, c) = if c { if c { h(x) } else { x } } else { x } — the call in
    // the innermost branch retires three frames at once: both If frames and
    // f's own, since each ret in the chain points at the next FnEnd.
    let tape = run(
        vec![
            Sized(FnStart, 3),                           // 0  h = fn(a) a * 2
            Var { elem: 0 },                             // 1
            Int(2),                                      // 2
            Sized(Bin(BinOp::Mul), 0),                   // 3
            Sized(FnEnd { args: 1 }, 3),                 // 4
            Sized(FnStart, 17),                          // 5  f
            Sized(FnStart, 10),                          // 6  outer then
            Sized(FnStart, 3),                           // 7  inner then: h(x)
            Ref { offset: 4 },                           // 8  -> h
            Var { elem: 0 },                             // 9
            Sized(Call { args: 1, comptime: false }, 0), // 10
            Sized(FnEnd { args: 0 }, 3),                 // 11
            Sized(FnStart, 1),                           // 12 inner else
            Var { elem: 0 },                             // 13
            Sized(FnEnd { args: 0 }, 1),                 // 14
            Var { elem: 1 },                             // 15
            Sized(If, 0),                                // 16
            Sized(FnEnd { args: 0 }, 10),                // 17
            Sized(FnStart, 1),                           // 18 outer else
            Var { elem: 0 },                             // 19
            Sized(FnEnd { args: 0 }, 1),                 // 20
            Var { elem: 1 },                             // 21
            Sized(If, 0),                                // 22
            Sized(FnEnd { args: 2 }, 17),                // 23
            Ref { offset: 1 },                           // 24 -> f
            Int(21),                                     // 25
            Int(1),                                      // 26
            Sized(Call { args: 2, comptime: false }, 0), // 27
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(42)));
}

#[test]
fn runtime_returned_closure_still_applies() {
    // apply(make_adder(3), 4) == 7, ported from the old crate: the call
    // inside apply is a tail call to a closure living below the floor.
    let tape = run(
        vec![
            Sized(FnStart, 3),                           // 0  adder = fn(n, x) n + x
            Var { elem: 0 },                             // 1
            Var { elem: 1 },                             // 2
            Sized(Bin(BinOp::Add), 0),                   // 3
            Sized(FnEnd { args: 2 }, 3),                 // 4
            Sized(FnStart, 3),                           // 5  make_adder = fn(n) [code, n]
            Ref { offset: 2 },                           // 6
            Var { elem: 0 },                             // 7
            Sized(List { elems: 2 }, 0),                 // 8
            Sized(FnEnd { args: 1 }, 3),                 // 9
            Sized(FnStart, 3),                           // 10 apply = fn(g, x) g(x)
            Var { elem: 0 },                             // 11
            Var { elem: 1 },                             // 12
            Sized(Call { args: 1, comptime: false }, 0), // 13
            Sized(FnEnd { args: 2 }, 3),                 // 14
            Ref { offset: 1 },                           // 15 -> apply
            Ref { offset: 7 },                           // 16 -> make_adder
            Int(3),                                      // 17
            Sized(Call { args: 1, comptime: false }, 0), // 18
            Int(4),                                      // 19
            Sized(Call { args: 2, comptime: false }, 0), // 20
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(7)));
}

#[test]
fn staged_countdown_reloads_and_runs_deep() {
    // countdown with g!() baked into the base case: the definition is staged
    // (the then-arm re-emits with the constant precomputed, the else-arm and
    // If defer), and the residual tape's recursive call must be detected as a
    // tail call at runtime with no emitter cooperation — depth 10^4 on staged
    // code.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 17),                          // 3  fn(self, n)
        Sized(FnStart, 2),                           // 4  then: g!()
        Ref { offset: 3 },                           // 5  -> g
        Sized(Call { args: 0, comptime: true }, 0),  // 6
        Sized(FnEnd { args: 0 }, 2),                 // 7
        Sized(FnStart, 7),                           // 8  else
        Var { elem: 0 },                             // 9
        Var { elem: 0 },                             // 10
        Sized(List { elems: 2 }, 0),                 // 11
        Var { elem: 1 },                             // 12
        Int(1),                                      // 13
        Sized(Bin(BinOp::Sub), 0),                   // 14
        Sized(Call { args: 1, comptime: false }, 0), // 15
        Sized(FnEnd { args: 0 }, 7),                 // 16
        Var { elem: 1 },                             // 17
        Int(0),                                      // 18
        Sized(Bin(BinOp::Eq), 0),                    // 19
        Sized(If, 0),                                // 20
        Sized(FnEnd { args: 2 }, 17),                // 21
        Ref { offset: 1 },                           // 22
        Ref { offset: 2 },                           // 23
        Sized(List { elems: 2 }, 0),                 // 24
    ]);
    let stage1 = run(prog, true);
    assert_eq!(reload_and_call(stage1, &[10_000]).last(), Some(&Int(5)));
}

// --- set and in-place mutation ---------------------------------------------------
// Set's operand order is [list, elem, index]. Take is two-phase: the take
// RESERVES (pushes a token, the binding stays readable), and the consuming op
// ACTIVATES (tombstones the binding, token becomes a borrow) — so reads of l
// emitted after `take l` but before the Set are legal, and read-modify-write
// needs no operand reordering.

#[test]
fn set_in_place_on_physical_list() {
    // set(9, 0, [1, 2, 3]) — the list is physical at the top, unobserved by
    // construction: the element slot is overwritten in place and the closing
    // compaction collects the spent operands below the extent.
    assert_eq!(
        run(
            vec![
                Int(1),
                Int(2),
                Int(3),
                Sized(List { elems: 3 }, 0),
                Int(9),
                Int(0),
                Sized(Set, 0),
            ],
            false
        ),
        [Int(9), Int(2), Int(3), Sized(List { elems: 3 }, 3)]
    );
}

#[test]
fn set_through_taken_arg_mutates() {
    // f(l) = get(set(9, 0, take l), 0) == 9 — the via-ref path: the take
    // removes the arg-slot observer, the scan between the list and the
    // operand finds nothing, and the element is written in place.
    let tape = run(
        vec![
            Sized(FnStart, 6),                           // 0  f
            Take { elem: 0 },                            // 1  list, reserved
            Int(9),                                      // 2  elem
            Int(0),                                      // 3  index
            Sized(Set, 0),                               // 4  activates the take
            Int(0),                                      // 5
            Sized(Get, 0),                               // 6
            Sized(FnEnd { args: 1 }, 6),                 // 7
            Ref { offset: 1 },                           // 8  -> f
            Int(1),                                      // 9
            Int(2),                                      // 10
            Sized(List { elems: 2 }, 0),                 // 11
            Sized(Call { args: 1, comptime: false }, 0), // 12
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(9)));
}

#[test]
fn set_with_live_observer_copies() {
    // f(l) = [set(9, 0, l), get(l, 0)] — no take, so the arg slot is a live
    // header observer: the set must copy, and the original must still read 1
    // afterwards. Copy-on-write is the semantics; in-place must be invisible.
    let tape = run(
        vec![
            Sized(FnStart, 8),                           // 0  f
            Var { elem: 0 },                             // 1  list, still observed
            Int(9),                                      // 2
            Int(0),                                      // 3
            Sized(Set, 0),                               // 4
            Var { elem: 0 },                             // 5
            Int(0),                                      // 6
            Sized(Get, 0),                               // 7
            Sized(List { elems: 2 }, 0),                 // 8
            Sized(FnEnd { args: 1 }, 8),                 // 9
            Ref { offset: 1 },                           // 10 -> f
            Int(1),                                      // 11
            Int(2),                                      // 12
            Sized(List { elems: 2 }, 0),                 // 13
            Sized(Call { args: 1, comptime: false }, 0), // 14
            Int(1),                                      // 15
            Sized(Get, 0),                               // 16
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(1)));
}

#[test]
fn set_of_elem_from_younger_list_copies() {
    // Regression for the forward-ref case that self-derived elems can't
    // produce: f(l, m) = set(take l, get(m, 0), 0) where m was built AFTER l,
    // so the elem is a ref pointing ABOVE l's element slot. Writing it in
    // place would create a forward ref; the guard must reject it and the copy
    // path must still wire the element correctly:
    // get(get(result, 0), 1) == 8. (The elem is computed after the take —
    // legal under two-phase reservation.)
    let tape = run(
        vec![
            Sized(FnStart, 10),                          // 0  f = fn(l, m)
            Take { elem: 0 },                            // 1  list = take l (reserved)
            Var { elem: 1 },                             // 2  get(m, 0)
            Int(0),                                      // 3
            Sized(Get, 0),                               // 4  -> ref into m, above l
            Int(0),                                      // 5  index
            Sized(Set, 0),                               // 6  forward ref -> copy path
            Int(0),                                      // 7
            Sized(Get, 0),                               // 8  -> the [7, 8] element
            Int(1),                                      // 9
            Sized(Get, 0),                               // 10 -> 8
            Sized(FnEnd { args: 2 }, 10),                // 11
            Ref { offset: 1 },                           // 12 -> f
            Int(1),                                      // 13 l = [1, 2], built first
            Int(2),                                      // 14
            Sized(List { elems: 2 }, 0),                 // 15
            Int(7),                                      // 16 m = [[7, 8]], built above
            Int(8),                                      // 17
            Sized(List { elems: 2 }, 0),                 // 18
            Sized(List { elems: 1 }, 0),                 // 19
            Sized(Call { args: 2, comptime: false }, 0), // 20
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(8)));
}

#[test]
fn set_out_of_bounds_errors() {
    let err = run_err(
        vec![Int(1), Sized(List { elems: 1 }, 0), Int(9), Int(5), Sized(Set, 0)],
        false,
    );
    assert_eq!(err, "List index is out of bounds");
}

#[test]
fn set_on_non_list_errors() {
    assert_eq!(
        run_err(vec![Int(7), Int(9), Int(0), Sized(Set, 0)], false),
        "Invalid list"
    );
}

#[test]
fn deferred_set_round_trips() {
    // f(x) = set([9], x, 0) — defers on the unresolved elem, keeps the list
    // inside the residual span, f(7) == [7].
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 7),                          // 3  f
        Ref { offset: 2 },                          // 4  -> g
        Sized(Call { args: 0, comptime: true }, 0), // 5
        Int(9),                                     // 6  list = [9]
        Sized(List { elems: 1 }, 0),                // 7
        Var { elem: 0 },                            // 8  elem (unresolved)
        Int(0),                                     // 9  index
        Sized(Set, 0),                              // 10
        Sized(FnEnd { args: 1 }, 7),                // 11
    ]);
    let stage1 = run(prog, true);
    let tape = reload_and_call(stage1, &[7]);
    let [.., a, Sized(List { elems: 1 }, _)] = tape[..] else {
        panic!("expected a 1-element list, got {:?}", &tape[tape.len() - 2..]);
    };
    assert_eq!(a, Int(7));
}

/// increment-map as a self-capturing closure over `l`, then `tail`:
/// map(self, l, i) = if len(l) == i { l }
///                   else { map(self, set(take l, i, get(l, i) + 1), i + 1) }
/// The take RESERVES l, the get still reads it, and the Set activates the
/// move — read-modify-write in one frame under the original operand order,
/// which is what two-phase Take exists for. `pad` prepends an inert blob so
/// the watermark test's peak sits clear of Vec's capacity-doubling
/// boundaries.
fn increment_map(pad: usize, l: &[i64], tail: &[Op]) -> Vec<Op> {
    let mut prog = vec![];
    if pad > 0 {
        prog.push(Sized(BlobStart, pad));
        prog.extend(std::iter::repeat(Int(0)).take(pad));
        prog.push(Sized(BlobEnd, pad));
    }
    prog.extend([
        Sized(FnStart, 25),                          // +0  fn(self, l, i)
        Sized(FnStart, 1),                           // +1  then: l
        Var { elem: 1 },                             // +2
        Sized(FnEnd { args: 0 }, 1),                 // +3
        Sized(FnStart, 15),                          // +4  else
        Var { elem: 0 },                             // +5  callee [self, self]
        Var { elem: 0 },                             // +6
        Sized(List { elems: 2 }, 0),                 // +7
        Take { elem: 1 },                            // +8  list = take l (reserved)
        Var { elem: 1 },                             // +9  elem = get(l, i) + 1
        Var { elem: 2 },                             // +10
        Sized(Get, 0),                               // +11
        Int(1),                                      // +12
        Sized(Bin(BinOp::Add), 0),                   // +13
        Var { elem: 2 },                             // +14 index = i
        Sized(Set, 0),                               // +15 activates the take
        Var { elem: 2 },                             // +16 i + 1
        Int(1),                                      // +17
        Sized(Bin(BinOp::Add), 0),                   // +18
        Sized(Call { args: 2, comptime: false }, 0), // +19
        Sized(FnEnd { args: 0 }, 15),                // +20
        Var { elem: 1 },                             // +21 cond: len(l) == i
        Sized(Len, 0),                               // +22
        Var { elem: 2 },                             // +23
        Sized(Bin(BinOp::Eq), 0),                    // +24
        Sized(If, 0),                                // +25
        Sized(FnEnd { args: 3 }, 25),                // +26
        Ref { offset: 1 },                           // +27
        Ref { offset: 2 },                           // +28
        Sized(List { elems: 2 }, 0),                 // +29
    ]);
    for &x in l {
        prog.push(Int(x));
    }
    prog.push(Sized(List { elems: l.len() }, 0));
    prog.push(Int(0));
    prog.push(Sized(Call { args: 2, comptime: false }, 0));
    prog.extend_from_slice(tail);
    prog
}

#[test]
fn map_increments_every_element() {
    // Small lists fail the walk's distance gate (frame junk > elems), so this
    // exercises the copy path end to end through the same program the
    // watermark test runs in place.
    let tape = run(increment_map(0, &[10, 20, 30], &[Int(2), Sized(Get, 0)]), false);
    assert_eq!(tape.last(), Some(&Int(31)));
    let tape = run(increment_map(0, &[10, 20, 30], &[Int(0), Sized(Get, 0)]), false);
    assert_eq!(tape.last(), Some(&Int(11)));
}

#[test]
fn map_over_taken_list_runs_in_place() {
    // The stage-4 milestone: in-place atomic map. The list lives below the
    // loop's floor and is mutated where it sits, so the value-region peak is
    // one list plus a bounded frame — with the blob pad, capacity stays at
    // one doubling (~6100). The copy path retains the original below the
    // floor for the whole loop and holds two copies per iteration, pushing
    // the peak past the next doubling (~12200).
    let n = 2000;
    let l: Vec<i64> = vec![0; n];
    let mut vm = Vm::load(increment_map(1000, &l, &[Int(1500), Sized(Get, 0)]));
    vm.run(false).expect("map(2000)");
    assert_eq!(vm.stack.last().map(|slot| slot.op), Some(Int(1)));
    assert!(vm.stack.capacity() < 8000, "stack peaked at {}", vm.stack.capacity());
}

#[test]
fn push_with_live_observer_preserves_the_original() {
    // f(l) = [push(l, 9), get(get(l, 0), 0)] with l = [[7, 8]] — the push
    // goes copy-on-write (the arg slot observes l), and the SHARED original
    // must stay fully intact: its ref-valued element slots are live storage
    // for every other observer, not spent handles. Consume-mode borrowing of
    // the old elements is only sound when the original is physical (provably
    // unobserved); via-ref it corrupts the original.
    let tape = run(
        vec![
            Sized(FnStart, 9),                           // 0  f
            Var { elem: 0 },                             // 1  push(l, 9)
            Int(9),                                      // 2
            Sized(Push { elems: 1 }, 0),                 // 3
            Var { elem: 0 },                             // 4  get(get(l, 0), 0)
            Int(0),                                      // 5
            Sized(Get, 0),                               // 6
            Int(0),                                      // 7
            Sized(Get, 0),                               // 8
            Sized(List { elems: 2 }, 0),                 // 9
            Sized(FnEnd { args: 1 }, 9),                 // 10
            Ref { offset: 1 },                           // 11 -> f
            Int(7),                                      // 12
            Int(8),                                      // 13
            Sized(List { elems: 2 }, 0),                 // 14 inner [7, 8]
            Sized(List { elems: 1 }, 0),                 // 15 l = [[7, 8]]
            Sized(Call { args: 1, comptime: false }, 0), // 16
            Int(1),                                      // 17
            Sized(Get, 0),                               // 18
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(7)));
}

#[test]
fn pop_with_live_observer_preserves_the_original() {
    // Same contract for Pop: f(l) = [pop1(l), get(get(l, 0), 1)] with
    // l = [[7, 8]] — the copy-path pop borrows the original's elements but
    // must not consume them while the original is observed.
    let tape = run(
        vec![
            Sized(FnStart, 8),                           // 0  f
            Var { elem: 0 },                             // 1  pop1(l)
            Sized(Pop { elems: 1 }, 0),                  // 2
            Var { elem: 0 },                             // 3  get(get(l, 0), 1)
            Int(0),                                      // 4
            Sized(Get, 0),                               // 5
            Int(1),                                      // 6
            Sized(Get, 0),                               // 7
            Sized(List { elems: 2 }, 0),                 // 8
            Sized(FnEnd { args: 1 }, 8),                 // 9
            Ref { offset: 1 },                           // 10 -> f
            Int(7),                                      // 11
            Int(8),                                      // 12
            Sized(List { elems: 2 }, 0),                 // 13 inner [7, 8]
            Sized(List { elems: 1 }, 0),                 // 14 l = [[7, 8]]
            Sized(Call { args: 1, comptime: false }, 0), // 15
            Int(1),                                      // 16
            Sized(Get, 0),                               // 17
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(8)));
}

#[test]
fn closure_call_with_multi_slot_arg_keeps_its_interior() {
    // The closure-arm gate for consume-mode arg normalization: a physical
    // multi-slot arg with ref-valued element slots. Only the operand's TOP
    // slot is a spent handle; borrowing must walk by value and never tombstone
    // interior slots. c = [code, code]; body(self, l) = get(get(l, 0), 1),
    // called with [[7, 8]] == 8.
    let tape = run(
        vec![
            Sized(FnStart, 5),                           // 0  fn(self, l)
            Var { elem: 1 },                             // 1
            Int(0),                                      // 2
            Sized(Get, 0),                               // 3
            Int(1),                                      // 4
            Sized(Get, 0),                               // 5
            Sized(FnEnd { args: 2 }, 5),                 // 6
            Ref { offset: 1 },                           // 7
            Ref { offset: 2 },                           // 8
            Sized(List { elems: 2 }, 0),                 // 9  c = [code, code]
            Int(7),                                      // 10
            Int(8),                                      // 11
            Sized(List { elems: 2 }, 0),                 // 12 inner [7, 8]
            Sized(List { elems: 1 }, 0),                 // 13 arg = [[7, 8]]
            Sized(Call { args: 1, comptime: false }, 0), // 14
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(8)));
}

// --- take and moved ------------------------------------------------------------

#[test]
fn take_of_a_borrowed_list_moves_the_handle() {
    // f(x) = get(take x, 1) — the common case: the arg slot holds a borrow,
    // take pushes a rebased handle and tombstones the binding.
    let tape = run(
        vec![
            Sized(FnStart, 3),                           // 0  f
            Take { elem: 0 },                            // 1
            Int(1),                                      // 2
            Sized(Get, 0),                               // 3
            Sized(FnEnd { args: 1 }, 3),                 // 4
            Ref { offset: 1 },                           // 5  -> f
            Int(7),                                      // 6
            Int(9),                                      // 7
            Sized(List { elems: 2 }, 0),                 // 8
            Sized(Call { args: 1, comptime: false }, 0), // 9
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(9)));
}

#[test]
fn take_of_an_int_moves_the_value() {
    // f(x) = take x + 1, f(41) == 42 — atoms move by copy; the binding still
    // dies (see use_after_take_errors), keeping the tripwire type-independent.
    let tape = run(
        vec![
            Sized(FnStart, 3),                           // 0  f
            Take { elem: 0 },                            // 1
            Int(1),                                      // 2
            Sized(Bin(BinOp::Add), 0),                   // 3
            Sized(FnEnd { args: 1 }, 3),                 // 4
            Ref { offset: 1 },                           // 5  -> f
            Int(41),                                     // 6
            Sized(Call { args: 1, comptime: false }, 0), // 7
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(42)));
}

#[test]
fn take_of_an_empty_list_arg() {
    // f(x) = len(take x), f([]) == 0 — an empty list is one slot, so it is
    // passed in place and sits in the arg slot as a value. Regression: the
    // fallback borrow arm would push a ref AT the arg slot and then tombstone
    // it, dangling the result onto Moved; empty lists must move by copy.
    let tape = run(
        vec![
            Sized(FnStart, 2),                           // 0  f
            Take { elem: 0 },                            // 1
            Sized(Len, 0),                               // 2
            Sized(FnEnd { args: 1 }, 2),                 // 3
            Ref { offset: 1 },                           // 4  -> f
            Sized(List { elems: 0 }, 0),                 // 5
            Sized(Call { args: 1, comptime: false }, 0), // 6
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(0)));
}

#[test]
fn use_after_take_errors() {
    // f(x) = [set(take x, 0, 9), x] — under two-phase take, use-after-move
    // means reading the binding after a consumer ACTIVATED the move: the Set
    // tombstones the slot, so the Var afterwards is the error Moved exists to
    // catch (without it, the read would silently observe the mutation).
    let err = run_err(
        vec![
            Sized(FnStart, 6),                           // 0  f
            Take { elem: 0 },                            // 1  reserved
            Int(9),                                      // 2
            Int(0),                                      // 3
            Sized(Set, 0),                               // 4  activated here
            Var { elem: 0 },                             // 5  read after the move
            Sized(List { elems: 2 }, 0),                 // 6
            Sized(FnEnd { args: 1 }, 6),                 // 7
            Ref { offset: 1 },                           // 8  -> f
            Int(1),                                      // 9
            Sized(List { elems: 1 }, 0),                 // 10
            Sized(Call { args: 1, comptime: false }, 0), // 11
        ],
        false,
    );
    assert_eq!(err, "Use after move");
}

#[test]
fn take_reserves_without_excluding_reads() {
    // f(x) = [take x, x] — the OLD use-after-move shape, now legal by design:
    // a reservation permits reads until a consumer activates it. Here the
    // List is the consumer, so both elements see x. get(f(5), 0) == 5.
    let tape = run(
        vec![
            Sized(FnStart, 3),                           // 0  f
            Take { elem: 0 },                            // 1  reserved
            Var { elem: 0 },                             // 2  still readable
            Sized(List { elems: 2 }, 0),                 // 3  activates the take
            Sized(FnEnd { args: 1 }, 3),                 // 4
            Ref { offset: 1 },                           // 5  -> f
            Int(5),                                      // 6
            Sized(Call { args: 1, comptime: false }, 0), // 7
            Int(0),                                      // 8
            Sized(Get, 0),                               // 9
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(5)));
}

#[test]
fn returning_a_taken_list_moves_it_out() {
    // f(l) = take l — a token as the return value: FnEnd is the consumer and
    // activates the move while the frame is still alive.
    let tape = run(
        vec![
            Sized(FnStart, 1),                           // 0  f
            Take { elem: 0 },                            // 1
            Sized(FnEnd { args: 1 }, 1),                 // 2
            Ref { offset: 1 },                           // 3  -> f
            Int(1),                                      // 4
            Int(2),                                      // 5
            Sized(List { elems: 2 }, 0),                 // 6
            Sized(Call { args: 1, comptime: false }, 0), // 7
            Int(1),                                      // 8
            Sized(Get, 0),                               // 9
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(2)));
}

#[test]
fn push_of_element_derived_from_taken_list() {
    // f(l) = push(take l, get(l, 0) + get(l, 1)) — the fib/prefix-sum shape:
    // the pushed element derives from the very list being moved. Two-phase
    // reservation makes this expressible with Push's unchanged list-first
    // operand order — the other front of the operand-order debate, settled by
    // test. get(f([1, 2]), 2) == 3.
    let tape = run(
        vec![
            Sized(FnStart, 9),                           // 0  f
            Take { elem: 0 },                            // 1  list (reserved)
            Var { elem: 0 },                             // 2  get(l, 0)
            Int(0),                                      // 3
            Sized(Get, 0),                               // 4
            Var { elem: 0 },                             // 5  get(l, 1)
            Int(1),                                      // 6
            Sized(Get, 0),                               // 7
            Sized(Bin(BinOp::Add), 0),                   // 8
            Sized(Push { elems: 1 }, 0),                 // 9  activates the take
            Sized(FnEnd { args: 1 }, 9),                 // 10
            Ref { offset: 1 },                           // 11 -> f
            Int(1),                                      // 12
            Int(2),                                      // 13
            Sized(List { elems: 2 }, 0),                 // 14
            Sized(Call { args: 1, comptime: false }, 0), // 15
            Int(2),                                      // 16
            Sized(Get, 0),                               // 17
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(3)));
}

#[test]
fn double_take_errors() {
    let err = run_err(
        vec![
            Sized(FnStart, 3),                           // 0  f
            Take { elem: 0 },                            // 1
            Take { elem: 0 },                            // 2
            Sized(List { elems: 2 }, 0),                 // 3
            Sized(FnEnd { args: 1 }, 3),                 // 4
            Ref { offset: 1 },                           // 5  -> f
            Int(5),                                      // 6
            Sized(Call { args: 1, comptime: false }, 0), // 7
        ],
        false,
    );
    assert_eq!(err, "Use after move");
}

#[test]
fn take_at_top_level_errors() {
    assert_eq!(run_err(vec![Take { elem: 0 }], false), "No active call frame");
}

/// f(x, c) = if c { get(take x, 0) } else { get(x, 0) }, called with ([7], c).
fn branch_dependent_take(c: i64) -> Vec<Op> {
    vec![
        Sized(FnStart, 12),                          // 0  f
        Sized(FnStart, 3),                           // 1  then: get(take x, 0)
        Take { elem: 0 },                            // 2
        Int(0),                                      // 3
        Sized(Get, 0),                               // 4
        Sized(FnEnd { args: 0 }, 3),                 // 5
        Sized(FnStart, 3),                           // 6  else: get(x, 0)
        Var { elem: 0 },                             // 7
        Int(0),                                      // 8
        Sized(Get, 0),                               // 9
        Sized(FnEnd { args: 0 }, 3),                 // 10
        Var { elem: 1 },                             // 11
        Sized(If, 0),                                // 12
        Sized(FnEnd { args: 2 }, 12),                // 13
        Ref { offset: 1 },                           // 14 -> f
        Int(7),                                      // 15
        Sized(List { elems: 1 }, 0),                 // 16
        Int(c),                                      // 17
        Sized(Call { args: 2, comptime: false }, 0), // 18
    ]
}

#[test]
fn take_in_the_taken_branch_works() {
    // Branch-dependent last use is the pattern Take exists for: only the
    // branch that actually runs consumes the binding.
    assert_eq!(run(branch_dependent_take(1), false).last(), Some(&Int(7)));
}

#[test]
fn take_in_the_untaken_branch_is_inert() {
    // ... and when the other branch runs, the take never fires, so the plain
    // Var read must succeed.
    assert_eq!(run(branch_dependent_take(0), false).last(), Some(&Int(7)));
}

// --- take: comptime ------------------------------------------------------------

#[test]
fn symbolic_take_re_emits_itself() {
    // f(x) = { g!(); get(take x, 0) } — pushing a value during a symbolic walk
    // IS emitting residual code, so take must re-emit as Take, not Var: a Var
    // would be semantically fine but silently lose the move from the runtime
    // stage. The residual is asserted exactly, then re-run for the
    // stage-uniformity check.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 5),                          // 3  f
        Ref { offset: 2 },                          // 4  -> g
        Sized(Call { args: 0, comptime: true }, 0), // 5
        Take { elem: 0 },                           // 6
        Int(0),                                     // 7
        Sized(Get, 0),                              // 8
        Sized(FnEnd { args: 1 }, 5),                // 9
    ]);
    let stage1 = run(prog, true);
    assert_eq!(
        stage1,
        [
            Sized(FnStart, 3),
            Take { elem: 0 },
            Int(0),
            Sized(Get, 2),
            Sized(FnEnd { args: 1 }, 3),
        ]
    );
    let tape = reload_and_call_with(stage1, &[vec![Int(8), Sized(List { elems: 1 }, 0)]]);
    assert_eq!(tape.last(), Some(&Int(8)));
}

#[test]
fn symbolic_take_does_not_poison_the_sibling_branch() {
    // f(x, c) = if c { g!(); get(take x, 0) } else { g!(); get(x, 0) } — both
    // branch thunks contain comptime calls, so BOTH are symbolically executed
    // under the shared frame. The take in the then-arm must not tombstone the
    // synthetic arg slot, or the else-arm's legitimate Var would be a false
    // use-after-move at comptime for a program that is fine at runtime (only
    // one branch ever runs). The run(prog, true) succeeding is the guard.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 16),                         // 3  f
        Sized(FnStart, 5),                          // 4  then
        Ref { offset: 3 },                          // 5  -> g
        Sized(Call { args: 0, comptime: true }, 0), // 6
        Take { elem: 0 },                           // 7
        Int(0),                                     // 8
        Sized(Get, 0),                              // 9
        Sized(FnEnd { args: 0 }, 5),                // 10
        Sized(FnStart, 5),                          // 11 else
        Ref { offset: 10 },                         // 12 -> g
        Sized(Call { args: 0, comptime: true }, 0), // 13
        Var { elem: 0 },                            // 14
        Int(0),                                     // 15
        Sized(Get, 0),                              // 16
        Sized(FnEnd { args: 0 }, 5),                // 17
        Var { elem: 1 },                            // 18
        Sized(If, 0),                               // 19
        Sized(FnEnd { args: 2 }, 16),               // 20
    ]);
    let stage1 = run(prog, true);
    assert!(
        stage1.iter().any(|op| matches!(op, Take { elem: 0 })),
        "expected the re-emitted take in the residual then-arm, got {stage1:?}"
    );
    let list_arg = vec![Int(7), Sized(List { elems: 1 }, 0)];
    let taken = reload_and_call_with(stage1.clone(), &[list_arg.clone(), vec![Int(1)]]);
    assert_eq!(taken.last(), Some(&Int(7)));
    let untaken = reload_and_call_with(stage1, &[list_arg, vec![Int(0)]]);
    assert_eq!(untaken.last(), Some(&Int(7)));
}

#[test]
fn call_with_taken_arg_defers() {
    // f(x) = { g!(); h(take x) } with h unannotated — a Take operand is
    // neither a Var (inlining a move would need linearity analysis) nor a
    // value, so the call residualizes with the take inside its span, and the
    // move fires when the residual runs.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 3),                           // 3  h = fn(a) a * 2
        Var { elem: 0 },                             // 4
        Int(2),                                      // 5
        Sized(Bin(BinOp::Mul), 0),                   // 6
        Sized(FnEnd { args: 1 }, 3),                 // 7
        Sized(FnStart, 5),                           // 8  f
        Ref { offset: 7 },                           // 9  -> g
        Sized(Call { args: 0, comptime: true }, 0),  // 10
        Ref { offset: 4 },                           // 11 -> h
        Take { elem: 0 },                            // 12
        Sized(Call { args: 1, comptime: false }, 0), // 13
        Sized(FnEnd { args: 1 }, 5),                 // 14
    ]);
    let stage1 = run(prog, true);
    assert!(
        stage1.iter().any(|op| matches!(op, Sized(Call { .. }, _))),
        "expected a residual call span, got {stage1:?}"
    );
    assert_eq!(reload_and_call(stage1, &[9]).last(), Some(&Int(18)));
}
