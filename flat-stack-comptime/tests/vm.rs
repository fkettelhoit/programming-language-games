use Op::*;
use SizedOp::*;
use flat_stack_comptime::{BinOp, Op, SizedOp, Vm};

fn run(program: Vec<Op>, comptime: bool) -> Vec<Op> {
    let mut vm = Vm::load(program);
    if let Err(e) = vm.run(comptime) {
        panic!("VM error: {e}\n{vm:#?}");
    }
    vm.stack.into_iter().map(|slot| slot.op).collect()
}

/// Run and return only the working region (everything above the program prefix).
fn values(program: Vec<Op>, comptime: bool) -> Vec<Op> {
    let prefix = program.len();
    let tape = run(program, comptime);
    tape[prefix..].to_vec()
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

/// `g = fn() 5` — the comptime-applied function used by the bodies below.
fn g() -> Vec<Op> {
    vec![Sized(FnStart, 1), Int(5), Sized(FnEnd { args: 0 }, 1)]
}

// --- residual calls ----------------------------------------------------------

#[test]
fn residual_call_is_measured_and_left_on_the_tape() {
    // At comptime a runtime call is not applied but rewritten with its span,
    // covering callee + args, so the whole expression stays skippable in O(1).
    // Regression: the arm once forgot to advance ip (infinite loop), and once
    // measured only the args, so compaction collected the callee.
    assert_eq!(
        values(vec![Int(1), Sized(Call { args: 0, comptime: false }, 0)], true),
        [Int(1), Sized(Call { args: 0, comptime: false }, 1)]
    );
}

// --- comptime evaluation of function bodies ----------------------------------

#[test]
fn body_without_comptime_calls_stays_in_prefix() {
    // A body containing no comptime calls is never re-emitted: its value is a
    // handle into the prefix, exactly as at runtime.
    assert_eq!(
        values(vec![Sized(FnStart, 1), Var { elem: 0 }, Sized(FnEnd { args: 1 }, 1)], true),
        [Ref { offset: 1 }]
    );
}

#[test]
fn body_collapses_to_constant_two_args() {
    // f(x, y) = g()! — the call to g runs at comptime and the residual f is a
    // constant function. Regression: re-bracketing paniced for args > 1 when
    // the return fast path had truncated the var slots.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 2),                          // 3  f
        Ref { offset: 2 },                          // 4  -> g
        Sized(Call { args: 0, comptime: true }, 0), // 5
        Sized(FnEnd { args: 2 }, 2),                // 6
    ]);
    assert_eq!(
        values(prog, true),
        [
            Ref { offset: 5 }, // handle to g, still in the prefix
            Sized(FnStart, 1),
            Int(5),
            Sized(FnEnd { args: 2 }, 1),
        ]
    );
}

#[test]
fn body_collapses_to_constant_one_arg() {
    // Same as above with one arg. Regression: the splice-based re-bracketing
    // replaced the computed result with the FuncStart, emitting an empty body.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 2),                          // 3  f
        Ref { offset: 2 },                          // 4  -> g
        Sized(Call { args: 0, comptime: true }, 0), // 5
        Sized(FnEnd { args: 1 }, 2),                // 6
    ]);
    assert_eq!(
        values(prog, true),
        [Ref { offset: 5 }, Sized(FnStart, 1), Int(5), Sized(FnEnd { args: 1 }, 1),]
    );
}

#[test]
fn body_with_vars_re_emits_them_in_place() {
    // f(x) = [x, x, g()!] — parameters are copied through as Var ops (vars are
    // atoms) and stay inside their bracket, so the residual needs no ref->var
    // rewrite and no shifting. Regression: vars were once borrowed as refs to
    // the scaffold slots, which dangled after re-bracketing.
    //
    // Comptime returns always compact, so the residual is canonical: the
    // scaffold arg slot is collected and extents are tight.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 5),                          // 3  f
        Var { elem: 0 },                            // 4
        Var { elem: 0 },                            // 5
        Ref { offset: 4 },                          // 6  -> g
        Sized(Call { args: 0, comptime: true }, 0), // 7
        Sized(List { elems: 3 }, 0),                // 8
        Sized(FnEnd { args: 1 }, 5),                // 9
    ]);
    assert_eq!(
        values(prog, true),
        [
            Ref { offset: 8 },
            Sized(FnStart, 4),
            Var { elem: 0 },
            Var { elem: 0 },
            Int(5),
            Sized(List { elems: 3 }, 3),
            Sized(FnEnd { args: 1 }, 4),
        ]
    );
}

#[test]
fn body_returning_its_own_var_re_brackets() {
    // f(x) = { g()!; x } — the result is an unresolved var. Regression: the
    // compact path resolved the return value through the var and failed with
    // "Unresolved var on the output stack"; vars must be atomic return values.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 3),                          // 3  f
        Ref { offset: 2 },                          // 4  -> g
        Sized(Call { args: 0, comptime: true }, 0), // 5
        Var { elem: 0 },                            // 6
        Sized(FnEnd { args: 1 }, 3),                // 7
    ]);
    assert_eq!(
        values(prog, true),
        [Ref { offset: 6 }, Sized(FnStart, 1), Var { elem: 0 }, Sized(FnEnd { args: 1 }, 1),]
    );
}

#[test]
fn top_level_thunk_with_comptime_call_walks() {
    // thunk = fn() g()! defined at the top level: the 0-arg bracket inherits
    // its frame from the enclosing one, but at the top level there is none —
    // the fallback is an empty frame (no vars are in scope). Regression: this
    // used to fail with "No active call frame".
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 2),                          // 3  thunk
        Ref { offset: 2 },                          // 4  -> g
        Sized(Call { args: 0, comptime: true }, 0), // 5
        Sized(FnEnd { args: 0 }, 2),                // 6
    ]);
    let prefix = prog.len();
    let stage1 = run(prog, true);
    assert_eq!(
        stage1[prefix..],
        [
            Ref { offset: 5 }, // handle to g, still in the prefix
            Sized(FnStart, 1),
            Int(5),
            Sized(FnEnd { args: 0 }, 1),
        ]
    );
    assert_eq!(reload_and_call(stage1, &[]).last(), Some(&Int(5)));
}

// --- staging round trips -----------------------------------------------------

#[test]
fn residual_function_round_trip() {
    // The definitional property of the experiment: the comptime output tape is
    // a valid input tape, and the residual function computes the same result
    // as the original would have. f(x) = [x, x, g()!], then f(7) at runtime.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 5),                          // 3  f
        Var { elem: 0 },                            // 4
        Var { elem: 0 },                            // 5
        Ref { offset: 4 },                          // 6  -> g
        Sized(Call { args: 0, comptime: true }, 0), // 7
        Sized(List { elems: 3 }, 0),                // 8
        Sized(FnEnd { args: 1 }, 5),                // 9
    ]);
    let stage1 = run(prog, true);
    let tape = reload_and_call(stage1, &[7]);
    let [.., a, b, c, Sized(List { elems: 3 }, _)] = tape[..] else {
        panic!("expected a 3-element list, got {:?}", &tape[tape.len() - 4..]);
    };
    assert_eq!([a, b, c], [Int(7), Int(7), Int(5)]);
}

#[test]
fn comptime_call_with_unresolved_arg_is_inlined() {
    // The mechanism from notes/2026/08/16: g2(y) = f(y)! with f(x) = [x, 1]
    // and y unresolved at comptime. f's arg slot holds the op Var{0}, every
    // use of x copies it through (substitution by value), f's frame dissolves,
    // and the copied var lands back inside g2's bracket, still naming elem 0 —
    // no frame tracking, no shifting.
    let prog = vec![
        Sized(FnStart, 3),                          // 0  f = fn(x) [x, 1]
        Var { elem: 0 },                            // 1
        Int(1),                                     // 2
        Sized(List { elems: 2 }, 0),                // 3
        Sized(FnEnd { args: 1 }, 3),                // 4
        Sized(FnStart, 3),                          // 5  g2 = fn(y) f(y)!
        Ref { offset: 2 },                          // 6  -> f
        Var { elem: 0 },                            // 7
        Sized(Call { args: 1, comptime: true }, 0), // 8
        Sized(FnEnd { args: 1 }, 3),                // 9
    ];
    let prefix = prog.len();
    let stage1 = run(prog, true);
    // the call to f is gone from the residual: f was applied at comptime
    assert!(
        !stage1[prefix..].iter().any(|op| matches!(op, Sized(Call { .. }, _))),
        "expected no residual call, got {:?}",
        &stage1[prefix..]
    );
    // ... and the residual g2 still computes [y, 1]
    let tape = reload_and_call(stage1, &[7]);
    let [.., a, b, Sized(List { elems: 2 }, _)] = tape[..] else {
        panic!("expected a 2-element list, got {:?}", &tape[tape.len() - 3..]);
    };
    assert_eq!([a, b], [Int(7), Int(1)]);
}

#[test]
fn nested_comptime_function_is_emitted_and_called_in_stage() {
    // g3(y) = { inner(z) = [z, k()!]; inner(y)! } — inner is re-emitted onto
    // the stack (its body contains a comptime call), and the comptime call to
    // inner then jumps into that freshly emitted bracket: code above the
    // original program prefix executes, which the unified representation
    // supports with no extra machinery. The consumed bracket is collected by
    // compaction and only its result [y, 5] survives into g3's residual.
    let prog = vec![
        Sized(FnStart, 1),                          // 0  k = fn() 5
        Int(5),                                     // 1
        Sized(FnEnd { args: 0 }, 1),                // 2
        Sized(FnStart, 8),                          // 3  g3
        Sized(FnStart, 4),                          // 4  inner
        Var { elem: 0 },                            // 5
        Ref { offset: 4 },                          // 6  -> k
        Sized(Call { args: 0, comptime: true }, 0), // 7
        Sized(List { elems: 2 }, 0),                // 8
        Sized(FnEnd { args: 1 }, 4),                // 9
        Var { elem: 0 },                            // 10
        Sized(Call { args: 1, comptime: true }, 0), // 11
        Sized(FnEnd { args: 1 }, 8),                // 12
    ];
    let prefix = prog.len();
    let stage1 = run(prog, true);
    assert!(
        !stage1[prefix..].iter().any(|op| matches!(op, Sized(Call { .. }, _))),
        "expected no residual call, got {:?}",
        &stage1[prefix..]
    );
    let tape = reload_and_call(stage1, &[7]);
    let [.., a, b, Sized(List { elems: 2 }, _)] = tape[..] else {
        panic!("expected a 2-element list, got {:?}", &tape[tape.len() - 3..]);
    };
    assert_eq!([a, b], [Int(7), Int(5)]);
}

// --- the 2026/08/16 example --------------------------------------------------

#[test]
fn blog_example_defers_to_the_inlined_conditional() {
    // The full example from notes/2026/08/16, closure-converted:
    //
    //   f(x, y') = if (x == y') { 1 } else { 0 }
    //   outer(y) = f(y, y)!
    //
    // Substitution links x and y': both of f's arg slots hold the same op
    // Var{0}. By design, comptime and runtime agree, so Eq does not decide
    // symbolically even here: Eq is int-only, and `x == x` is 1 for ints but
    // an error for lists, so deciding it would bake a type assumption into
    // the residual. Instead the whole call inlines and defers: f's frame
    // dissolves, and the residual outer is `if (y == y) { 1 } else { 0 }`
    // with the decision moved to runtime.
    let prog = vec![
        Sized(FnStart, 10),                         // 0  f
        Sized(FnStart, 1),                          // 1  then
        Int(1),                                     // 2
        Sized(FnEnd { args: 0 }, 1),                // 3
        Sized(FnStart, 1),                          // 4  else
        Int(0),                                     // 5
        Sized(FnEnd { args: 0 }, 1),                // 6
        Var { elem: 0 },                            // 7
        Var { elem: 1 },                            // 8
        Sized(Bin(BinOp::Eq), 0),                   // 9
        Sized(If, 0),                               // 10
        Sized(FnEnd { args: 2 }, 10),               // 11
        Sized(FnStart, 4),                          // 12 outer
        Ref { offset: 2 },                          // 13 -> f
        Var { elem: 0 },                            // 14
        Var { elem: 0 },                            // 15
        Sized(Call { args: 2, comptime: true }, 0), // 16
        Sized(FnEnd { args: 1 }, 4),                // 17
    ];
    let prefix = prog.len();
    let stage1 = run(prog, true);
    assert_eq!(
        stage1[prefix..],
        [
            Ref { offset: 7 }, // handle to f, still in the prefix
            Sized(FnStart, 6),
            Ref { offset: 17 }, // then-arm handle
            Ref { offset: 15 }, // else-arm handle
            Var { elem: 0 },
            Var { elem: 0 },
            Sized(Bin(BinOp::Eq), 2),
            Sized(If, 5),
            Sized(FnEnd { args: 1 }, 6),
        ]
    );
    let tape = reload_and_call(stage1, &[7]);
    assert_eq!(tape.last(), Some(&Int(1)));
}

#[test]
fn walked_arm_precomputes_its_comptime_call() {
    // f(x) = if (x == 0) { g()! } else { 7 } — walking f's definition walks
    // the then-arm (it contains a comptime call), precomputes g()! to 5, and
    // re-emits the arm as a bracket; the condition and the If defer. The
    // residual still branches correctly at runtime.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 11),                         // 3  f
        Sized(FnStart, 2),                          // 4  then: g()!
        Ref { offset: 3 },                          // 5  -> g
        Sized(Call { args: 0, comptime: true }, 0), // 6
        Sized(FnEnd { args: 0 }, 2),                // 7
        Sized(FnStart, 1),                          // 8  else
        Int(7),                                     // 9
        Sized(FnEnd { args: 0 }, 1),                // 10
        Var { elem: 0 },                            // 11
        Int(0),                                     // 12
        Sized(Bin(BinOp::Eq), 0),                   // 13
        Sized(If, 0),                               // 14
        Sized(FnEnd { args: 1 }, 11),               // 15
    ]);
    let prefix = prog.len();
    let stage1 = run(prog, true);
    assert_eq!(
        stage1[prefix..],
        [
            Ref { offset: 14 }, // handle to g, still in the prefix
            Sized(FnStart, 8),
            Sized(FnStart, 1), // re-emitted then-arm ...
            Int(5),            // ... with g()! precomputed
            Sized(FnEnd { args: 0 }, 1),
            Ref { offset: 11 }, // else-arm handle
            Var { elem: 0 },
            Int(0),
            Sized(Bin(BinOp::Eq), 2),
            Sized(If, 7),
            Sized(FnEnd { args: 1 }, 8),
        ]
    );
    assert_eq!(reload_and_call(stage1.clone(), &[0]).last(), Some(&Int(5)));
    assert_eq!(reload_and_call(stage1, &[1]).last(), Some(&Int(7)));
}

#[test]
fn comptime_call_of_thunk_applies_runtime_calls_inside() {
    // f = fn() h(9), called as f()! — inside an applied comptime call,
    // unannotated calls execute (the reverse-via-fold case), including for
    // zero-arg functions.
    let prog = vec![
        Sized(FnStart, 3),                           // 0 h = fn(a) a * 2
        Var { elem: 0 },                             // 1
        Int(2),                                      // 2
        Sized(Bin(BinOp::Mul), 0),                   // 3
        Sized(FnEnd { args: 1 }, 3),                 // 4
        Sized(FnStart, 3),                           // 5 f
        Ref { offset: 2 },                           // 6 -> h
        Int(9),                                      // 7
        Sized(Call { args: 1, comptime: false }, 0), // 8
        Sized(FnEnd { args: 0 }, 3),                 // 9
        Ref { offset: 1 },                           // 10 -> f
        Sized(Call { args: 0, comptime: true }, 0),  // 11
    ];
    assert_eq!(values(prog, true).last(), Some(&Int(18)));
}

/// countdown as a self-capturing closure: c = [code, code]; c(3), with the
/// recursive call site annotated as given.
fn countdown(comptime_rec: bool) -> Vec<Op> {
    vec![
        Sized(FnStart, 16),                                 // 0
        Sized(FnStart, 1),                                  // 1  then
        Int(0),                                             // 2
        Sized(FnEnd { args: 0 }, 1),                        // 3
        Sized(FnStart, 7),                                  // 4  else
        Var { elem: 0 },                                    // 5
        Var { elem: 0 },                                    // 6
        Sized(List { elems: 2 }, 0),                        // 7
        Var { elem: 1 },                                    // 8
        Int(1),                                             // 9
        Sized(Bin(BinOp::Sub), 0),                          // 10
        Sized(Call { args: 1, comptime: comptime_rec }, 0), // 11
        Sized(FnEnd { args: 0 }, 7),                        // 12
        Var { elem: 1 },                                    // 13
        Int(0),                                             // 14
        Sized(Bin(BinOp::Eq), 0),                           // 15
        Sized(If, 0),                                       // 16
        Sized(FnEnd { args: 2 }, 16),                       // 17
        Ref { offset: 1 },                                  // 18
        Ref { offset: 2 },                                  // 19
        Sized(List { elems: 2 }, 0),                        // 20
        Int(3),                                             // 21
        Sized(Call { args: 1, comptime: true }, 0),         // 22
    ]
}

#[test]
fn comptime_recursion_with_annotated_call_evaluates() {
    // countdown(3)! with the recursive call also annotated: processing the
    // definition defers the recursive call (its closure's code element is an
    // unresolved var), and the top-level application then runs the recursion
    // lazily through If, terminating via the base case exactly as at runtime.
    let tape = run(countdown(true), true);
    assert_eq!(tape.last(), Some(&Int(0)));
}

#[test]
fn comptime_recursion_with_plain_call_evaluates() {
    // Same, but the recursive call is a plain runtime call: inside an applied
    // comptime call, unannotated calls execute (the reverse-via-fold rule),
    // so the recursion still runs to completion at comptime.
    let tape = run(countdown(false), true);
    assert_eq!(tape.last(), Some(&Int(0)));
}

#[test]
fn deferred_call_in_a_list_round_trips() {
    // f(x) = [g()!, if (1 == 1) { h(7) } else { 0 }] — the condition is
    // static, so the If disappears at comptime and the unannotated h(7)
    // survives as a deferred call. The list containing it must stay
    // unnormalized: a handle to a deferred span would dangle after reload,
    // because computations, unlike values, are not self-evaluating.
    let prog = vec![
        Sized(FnStart, 1),                           // 0  g
        Int(5),                                      // 1
        Sized(FnEnd { args: 0 }, 1),                 // 2
        Sized(FnStart, 3),                           // 3  h = fn(a) a * 2
        Var { elem: 0 },                             // 4
        Int(2),                                      // 5
        Sized(Bin(BinOp::Mul), 0),                   // 6
        Sized(FnEnd { args: 1 }, 3),                 // 7
        Sized(FnStart, 15),                          // 8  f
        Ref { offset: 7 },                           // 9  -> g
        Sized(Call { args: 0, comptime: true }, 0),  // 10
        Sized(FnStart, 3),                           // 11 then: h(7)
        Ref { offset: 5 },                           // 12 -> h
        Int(7),                                      // 13
        Sized(Call { args: 1, comptime: false }, 0), // 14
        Sized(FnEnd { args: 0 }, 3),                 // 15
        Sized(FnStart, 1),                           // 16 else
        Int(0),                                      // 17
        Sized(FnEnd { args: 0 }, 1),                 // 18
        Int(1),                                      // 19
        Int(1),                                      // 20
        Sized(Bin(BinOp::Eq), 0),                    // 21
        Sized(If, 0),                                // 22
        Sized(List { elems: 2 }, 0),                 // 23
        Sized(FnEnd { args: 1 }, 15),                // 24
    ];
    let prefix = prog.len();
    let stage1 = run(prog, true);
    assert_eq!(
        stage1[prefix..],
        [
            Ref { offset: 23 }, // handle to g
            Ref { offset: 19 }, // handle to h
            Sized(FnStart, 5),
            Int(5),             // g()! precomputed
            Ref { offset: 22 }, // -> h
            Int(7),
            Sized(Call { args: 1, comptime: false }, 2), // h(7), deferred
            Sized(List { elems: 2 }, 4),                 // unnormalized list
            Sized(FnEnd { args: 1 }, 5),
        ]
    );
    // reload, call f(9), and read element 1 of the result
    let mut stage2 = stage1;
    let f_end = stage2.len() - 1;
    stage2.push(Ref { offset: stage2.len() - f_end });
    stage2.push(Int(9));
    stage2.push(Sized(Call { args: 1, comptime: false }, 0));
    stage2.push(Int(1));
    stage2.push(Sized(Get, 0));
    let tape = run(stage2, false);
    assert_eq!(tape.last(), Some(&Int(14)));
}

#[test]
fn compacted_list_return_drops_dead_bulk() {
    // f(x) = { g()!; [[1, 2], 3] } — normalizing the outer list copies Int(3)
    // up as a handle, leaving a dead bulk copy inside the marker's extent.
    // Compaction on the symbolic return must use precise element marking for
    // a normalized list (elements are one slot each) so the dead copy is
    // collected. Regression: the guard once compared the element span against
    // 0 instead of n, sending every non-empty list down the full-extent path
    // and retaining the garbage.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 7),                          // 3  f
        Ref { offset: 2 },                          // 4  -> g
        Sized(Call { args: 0, comptime: true }, 0), // 5
        Int(1),                                     // 6
        Int(2),                                     // 7
        Sized(List { elems: 2 }, 0),                // 8
        Int(3),                                     // 9
        Sized(List { elems: 2 }, 0),                // 10
        Sized(FnEnd { args: 1 }, 7),                // 11
    ]);
    let prefix = prog.len();
    let stage1 = run(prog, true);
    assert_eq!(
        stage1[prefix..],
        [
            Ref { offset: 10 }, // handle to g
            Sized(FnStart, 6),
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 2),
            Ref { offset: 1 }, // element 0 -> inner list
            Int(3),            // element 1, dead bulk copy collected
            Sized(List { elems: 2 }, 5),
            Sized(FnEnd { args: 1 }, 6),
        ]
    );
    let tape = reload_and_call(stage1, &[0]);
    let [.., a, b, Sized(List { elems: 2 }, _)] = tape[..] else {
        panic!("expected a 2-element list, got {:?}", &tape[tape.len() - 3..]);
    };
    assert!(matches!(a, Ref { .. }), "element 0 should be a handle, got {a:?}");
    assert_eq!(b, Int(3));
}

#[test]
fn comptime_call_with_deferred_span_arg_round_trips() {
    // KNOWN FAILING (see roadmap): outer(y) = f(h(y))! with h unannotated and
    // f(x) = [x]. The argument to the comptime call is a deferred span (h's
    // call residualizes during the walk), and the apply path normalizes it
    // into a ref-to-computation: push_borrows turns the span into a Ref in
    // f's arg slot, and f's body copies that ref into the residual list.
    // After reload the span re-executes by APPLYING — its result lands on top
    // of the stack — while the ref re-borrows its old target, which still
    // holds the input Call op: the element dangles. Values are
    // self-evaluating, computations are not, so no output ref may point at
    // one; the call must defer (keeping its comptime flag) instead of
    // applying. Once it does, the deferred call applies on reload and
    // get(outer(9), 0) == h(9) == 18.
    let prog = vec![
        Sized(FnStart, 3),                           // 0  h = fn(a) a * 2
        Var { elem: 0 },                             // 1
        Int(2),                                      // 2
        Sized(Bin(BinOp::Mul), 0),                   // 3
        Sized(FnEnd { args: 1 }, 3),                 // 4
        Sized(FnStart, 2),                           // 5  f = fn(x) [x]
        Var { elem: 0 },                             // 6
        Sized(List { elems: 1 }, 0),                 // 7
        Sized(FnEnd { args: 1 }, 2),                 // 8
        Sized(FnStart, 5),                           // 9  outer = fn(y) f(h(y))!
        Ref { offset: 2 },                           // 10 -> f
        Ref { offset: 7 },                           // 11 -> h
        Var { elem: 0 },                             // 12
        Sized(Call { args: 1, comptime: false }, 0), // 13
        Sized(Call { args: 1, comptime: true }, 0),  // 14
        Sized(FnEnd { args: 1 }, 5),                 // 15
    ];
    let stage1 = run(prog, true);
    // reload, call outer(9), and read element 0 of the result
    let mut stage2 = stage1;
    let f_end = stage2.len() - 1;
    stage2.push(Ref { offset: stage2.len() - f_end });
    stage2.push(Int(9));
    stage2.push(Sized(Call { args: 1, comptime: false }, 0));
    stage2.push(Int(0));
    stage2.push(Sized(Get, 0));
    let tape = run(stage2, false);
    assert_eq!(tape.last(), Some(&Int(18)));
}

// --- deferred operations -------------------------------------------------------

#[test]
fn deferred_ops_chain() {
    // f(x) = { g()!; (x + 1) + 1 } — the inner Bin defers on the unresolved
    // var, and the outer Bin must recognize the residual Bin span as a
    // deferred computation and defer too: computations are contagious.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 7),                          // 3 f
        Ref { offset: 2 },                          // 4 -> g
        Sized(Call { args: 0, comptime: true }, 0), // 5
        Var { elem: 0 },                            // 6
        Int(1),                                     // 7
        Sized(Bin(BinOp::Add), 0),                  // 8
        Int(1),                                     // 9
        Sized(Bin(BinOp::Add), 0),                  // 10
        Sized(FnEnd { args: 1 }, 7),                // 11
    ]);
    let stage1 = run(prog, true);
    let tape = reload_and_call(stage1, &[7]);
    assert_eq!(tape.last(), Some(&Int(9)));
}

#[test]
fn deferred_push_keeps_its_list() {
    // f(x) = push(x, [1]) — the residual span must include the list operand,
    // or compaction collects it out from under the deferred op.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 6),                          // 3 f
        Ref { offset: 2 },                          // 4 -> g
        Sized(Call { args: 0, comptime: true }, 0), // 5
        Int(1),                                     // 6
        Sized(List { elems: 1 }, 0),                // 7
        Var { elem: 0 },                            // 8
        Sized(Push { elems: 1 }, 0),                // 9
        Sized(FnEnd { args: 1 }, 6),                // 10
    ]);
    let stage1 = run(prog, true);
    let tape = reload_and_call(stage1, &[7]);
    let [.., a, b, Sized(List { elems: 2 }, _)] = tape[..] else {
        panic!("expected a 2-element list, got {:?}", &tape[tape.len() - 3..]);
    };
    assert_eq!([a, b], [Int(1), Int(7)]);
}

#[test]
fn deferred_push_onto_unresolved_list() {
    // f(x) = push(1, x) — the list operand itself is unresolved; the op
    // defers instead of failing on the var.
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 5),                          // 3 f
        Ref { offset: 2 },                          // 4 -> g
        Sized(Call { args: 0, comptime: true }, 0), // 5
        Var { elem: 0 },                            // 6
        Int(1),                                     // 7
        Sized(Push { elems: 1 }, 0),                // 8
        Sized(FnEnd { args: 1 }, 5),                // 9
    ]);
    let stage1 = run(prog, true);
    let tape = reload_and_call_with(stage1, &[vec![Int(2), Sized(List { elems: 1 }, 0)]]);
    let [.., a, b, Sized(List { elems: 2 }, _)] = tape[..] else {
        panic!("expected a 2-element list, got {:?}", &tape[tape.len() - 3..]);
    };
    assert_eq!([a, b], [Int(2), Int(1)]);
}

#[test]
fn comptime_call_with_resolved_args_fully_evaluates() {
    // f(xs) = len(xs), called as f([1, 2])! — a borrowed operand that
    // resolves to a value is not unresolved: the op evaluates and the whole
    // comptime call collapses to 2 on the tape.
    let prog = vec![
        Sized(FnStart, 2),                          // 0 f
        Var { elem: 0 },                            // 1
        Sized(Len, 0),                              // 2
        Sized(FnEnd { args: 1 }, 2),                // 3
        Ref { offset: 1 },                          // 4 -> f
        Int(1),                                     // 5
        Int(2),                                     // 6
        Sized(List { elems: 2 }, 0),                // 7
        Sized(Call { args: 1, comptime: true }, 0), // 8
    ];
    assert_eq!(values(prog, true).last(), Some(&Int(2)));
}

#[test]
fn deferred_get_round_trip() {
    // f(x) = get(x, 0) — defers on the unresolved list, f([8]) == 8
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 5),                          // 3 f
        Ref { offset: 2 },                          // 4 -> g
        Sized(Call { args: 0, comptime: true }, 0), // 5
        Var { elem: 0 },                            // 6
        Int(0),                                     // 7
        Sized(Get, 0),                              // 8
        Sized(FnEnd { args: 1 }, 5),                // 9
    ]);
    let stage1 = run(prog, true);
    let tape = reload_and_call_with(stage1, &[vec![Int(8), Sized(List { elems: 1 }, 0)]]);
    assert_eq!(tape.last(), Some(&Int(8)));
}

#[test]
fn deferred_set_round_trip() {
    // f(x) = set([9], x, 0) — defers on the unresolved element, keeping the
    // list inside the residual span, f(7) == [7]
    let mut prog = g();
    prog.extend([
        Sized(FnStart, 7),                          // 3 f
        Ref { offset: 2 },                          // 4 -> g
        Sized(Call { args: 0, comptime: true }, 0), // 5
        Int(9),                                     // 6
        Sized(List { elems: 1 }, 0),                // 7
        Var { elem: 0 },                            // 8
        Int(0),                                     // 9
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

// --- runtime smoke tests -----------------------------------------------------

#[test]
fn runtime_returned_closure_still_applies() {
    // apply(make_adder(3), 4) == 7 — guards the runtime path against the
    // comptime changes (vars copied by value in `borrow`, Option ret, etc.).
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
fn runtime_countdown_via_closure_still_works() {
    // c = [code, code]; c(3) == 0 — recursion via self-capture, exercising If
    // frames, Bin and closure splicing on the runtime path.
    let tape = run(
        vec![
            Sized(FnStart, 16),                          // 0
            Sized(FnStart, 1),                           // 1  then-arm
            Int(0),                                      // 2
            Sized(FnEnd { args: 0 }, 1),                 // 3
            Sized(FnStart, 7),                           // 4  else-arm
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
            Int(3),                                      // 21
            Sized(Call { args: 1, comptime: false }, 0), // 22
        ],
        false,
    );
    assert_eq!(tape.last(), Some(&Int(0)));
}
