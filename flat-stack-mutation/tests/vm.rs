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
    // f(x) = [take x, x] — reading a binding after moving out of it is the
    // one thing Moved exists to catch: without the tombstone, the second use
    // would silently observe whatever the first use's consumer did.
    let err = run_err(
        vec![
            Sized(FnStart, 3),                           // 0  f
            Take { elem: 0 },                            // 1
            Var { elem: 0 },                             // 2
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
