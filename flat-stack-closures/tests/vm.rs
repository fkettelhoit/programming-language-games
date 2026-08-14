use flat_stack_closures::{BinOp, Op, SizedOp, Vm};
use Op::*;
use SizedOp::*;

fn run(program: Vec<Op>) -> Vec<Op> {
    let mut vm = Vm::load(program);
    if let Err(e) = vm.run() {
        panic!("VM error: {e}\n{vm:#?}");
    }
    vm.stack.into_iter().map(|slot| slot.op).collect()
}

/// Run and return only the working region (everything above the program prefix).
fn values(program: Vec<Op>) -> Vec<Op> {
    let prefix = program.len();
    let tape = run(program);
    tape[prefix..].to_vec()
}

// --- pure data ---------------------------------------------------------------

#[test]
fn int_literal() {
    assert_eq!(values(vec![Int(42)]), [Int(42)]);
}

#[test]
fn empty_list() {
    assert_eq!(values(vec![Sized(List { elems: 0 }, 0)]), [Sized(List { elems: 0 }, 0)]);
}

#[test]
fn flat_list() {
    // [1, 2] — all elements atomic: no normalization
    assert_eq!(
        values(vec![Int(1), Int(2), Sized(List { elems: 2 }, 0)]),
        [Int(1), Int(2), Sized(List { elems: 2 }, 2)]
    );
}

#[test]
fn nested_list_normalizes() {
    // [[1, 2], 3] — compound element: bulk stays, one-slot handles appended
    assert_eq!(
        values(vec![
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 0),
            Int(3),
            Sized(List { elems: 2 }, 0)
        ]),
        [
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 2), // inner marker
            Int(3),                      // bulk copy (dead after normalization)
            Ref { offset: 2 },           // handle 0 -> inner marker
            Int(3),                      // handle 1
            Sized(List { elems: 2 }, 6), // outer marker
        ]
    );
}

// --- arithmetic ----------------------------------------------------------------

#[test]
fn bin_ops() {
    assert_eq!(values(vec![Int(40), Int(2), Sized(Bin(BinOp::Add), 0)]), [Int(42)]);
    assert_eq!(values(vec![Int(7), Int(2), Sized(Bin(BinOp::Sub), 0)]), [Int(5)]);
    assert_eq!(values(vec![Int(6), Int(7), Sized(Bin(BinOp::Mul), 0)]), [Int(42)]);
    assert_eq!(values(vec![Int(3), Int(3), Sized(Bin(BinOp::Eq), 0)]), [Int(1)]);
    assert_eq!(values(vec![Int(3), Int(4), Sized(Bin(BinOp::Eq), 0)]), [Int(0)]);
}

// --- functions ----------------------------------------------------------------

#[test]
fn func_bracket_evaluates_to_handle() {
    // λx. x — walking the bracket pushes a handle to its FuncEnd, never enters it
    assert_eq!(
        values(vec![Sized(FuncStart, 1), Var { elem: 0 }, Sized(FuncEnd { args: 1 }, 1)]),
        [Ref { offset: 1 }]
    );
}

#[test]
fn identity_call() {
    // (λx. x)(42) — return slides the atom down over the dead frame
    assert_eq!(
        values(vec![
            Sized(FuncStart, 1),
            Var { elem: 0 },
            Sized(FuncEnd { args: 1 }, 1),
            Int(42),
            Sized(Call { args: 1 }, 0),
        ]),
        [Int(42)]
    );
}

#[test]
fn constant_function_call() {
    // (λx. 7)(42)
    assert_eq!(
        values(vec![
            Sized(FuncStart, 1),
            Int(7),
            Sized(FuncEnd { args: 1 }, 1),
            Int(42),
            Sized(Call { args: 1 }, 0),
        ]),
        [Int(7)]
    );
}

#[test]
fn second_of_two_args() {
    // (λx y. y)(1, 2)
    assert_eq!(
        values(vec![
            Sized(FuncStart, 1),
            Var { elem: 1 },
            Sized(FuncEnd { args: 2 }, 1),
            Int(1),
            Int(2),
            Sized(Call { args: 2 }, 0),
        ]),
        [Int(2)]
    );
}

#[test]
fn calling_through_ref_twice() {
    // f = λx. x; f(1); f(2) — Ref instructions are stable ip-relative pointers,
    // calls through them are non-destructive.
    assert_eq!(
        values(vec![
            Sized(FuncStart, 1),
            Var { elem: 0 },
            Sized(FuncEnd { args: 1 }, 1),
            Ref { offset: 1 }, // at 3 -> FuncEnd at 2
            Int(1),
            Sized(Call { args: 1 }, 0),
            Ref { offset: 4 }, // at 6 -> FuncEnd at 2
            Int(2),
            Sized(Call { args: 1 }, 0),
        ]),
        [
            Ref { offset: 7 }, // unused handle from walking the bracket
            Int(1),
            Int(2),
        ]
    );
}

#[test]
fn call_with_list_arg() {
    // (λx. x)([1, 2]) — the returned borrow points into the dying frame; the
    // compaction squeezes the dead function handle and slides the list down,
    // so the caller receives the list itself at the frame floor.
    assert_eq!(
        values(vec![
            Sized(FuncStart, 1),
            Var { elem: 0 },
            Sized(FuncEnd { args: 1 }, 1),
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 0),
            Sized(Call { args: 1 }, 0),
        ]),
        [Int(1), Int(2), Sized(List { elems: 2 }, 2)]
    );
}

// --- blobs / refs ----------------------------------------------------------------

#[test]
fn blob_evaluates_to_handle() {
    assert_eq!(values(vec![Sized(BlobStart, 1), Int(999), Sized(BlobEnd, 1)]), [Ref { offset: 1 }]);
}

#[test]
fn ref_to_position_zero() {
    assert_eq!(values(vec![Int(9), Ref { offset: 1 }]), [Int(9), Int(9)]);
}

// --- Len ----------------------------------------------------------------

#[test]
fn len_through_ref() {
    // (λx. len(x))([1, 2]) — Len through a handle is non-destructive, O(1)
    assert_eq!(
        values(vec![
            Sized(FuncStart, 2),
            Var { elem: 0 },
            Sized(Len, 0),
            Sized(FuncEnd { args: 1 }, 2),
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 0),
            Sized(Call { args: 1 }, 0),
        ]),
        [Int(2)]
    );
}

#[test]
fn len_of_direct_list() {
    // len([1, 2]) — a direct list at the top is provably unreferenced (I2),
    // so Len consumes its entire extent and replaces it with the count.
    assert_eq!(values(vec![Int(1), Int(2), Sized(List { elems: 2 }, 0), Sized(Len, 0)]), [Int(2)]);
}

// --- Push ----------------------------------------------------------------
//
// Push never truncates and never compacts: the result is a list, so it
// discharges its operands by covering them — the new marker's slots span
// down to the base of the list operand (extent base if direct, handle slot
// if borrowed), swallowing old extent/handle, element bulk, and the stale
// handles as ghost data. The element count is static, like List's.

#[test]
fn push_atoms_onto_direct_list() {
    // push([1, 2], 4, 5) -> [1, 2, 4, 5]
    assert_eq!(
        values(vec![
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 0),
            Int(4),
            Int(5),
            Sized(Push { elems: 2 }, 0),
        ]),
        [
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 2), // old list, now ghost
            Int(4),
            Int(5),
            Int(1),                      // element 0
            Int(2),                      // element 1
            Int(4),                      // element 2
            Int(5),                      // element 3
            Sized(List { elems: 4 }, 9), // covers everything above
        ]
    );
}

#[test]
fn push_zero_elements() {
    // push([1]) -> [1] (fresh copy of the handles, old list adopted as ghost)
    assert_eq!(
        values(vec![Int(1), Sized(List { elems: 1 }, 0), Sized(Push { elems: 0 }, 0)]),
        [Int(1), Sized(List { elems: 1 }, 1), Int(1), Sized(List { elems: 1 }, 3)]
    );
}

#[test]
fn push_compound_element() {
    // push([9], [1, 2]) -> [9, [1, 2]] — the new element's handle must be a
    // rebased ref to the inline list, and the walk must step over its whole
    // extent.
    assert_eq!(
        values(vec![
            Int(9),
            Sized(List { elems: 1 }, 0),
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 0),
            Sized(Push { elems: 1 }, 0),
        ]),
        [
            Int(9),
            Sized(List { elems: 1 }, 1), // old list, ghost
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 2), // pushed element, owned inline
            Int(9),                      // element 0
            Ref { offset: 2 },           // element 1 -> inline list marker
            Sized(List { elems: 2 }, 7),
        ]
    );
}

#[test]
fn push_onto_borrowed_list() {
    // (λx. push(x, 4))([1, 2]) — the callee borrows the list; the new marker
    // covers only its own frame-local span (from the Var handle down), and
    // the return re-marks it to adopt the whole frame.
    assert_eq!(
        values(vec![
            Sized(FuncStart, 3),           // 0
            Var { elem: 0 },               // 1  x
            Int(4),                        // 2
            Sized(Push { elems: 1 }, 0),   // 3
            Sized(FuncEnd { args: 1 }, 3), // 4
            Int(1),                        // 5
            Int(2),                        // 6
            Sized(List { elems: 2 }, 0),   // 7
            Sized(Call { args: 1 }, 0),    // 8
        ]),
        [
            Ref { offset: 5 }, // function handle
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 2), // the argument list (still live: borrowed)
            Ref { offset: 1 },           // arg handle from Call normalization
            Ref { offset: 2 },           // Var borrow of x
            Int(4),
            Int(1),                       // element 0 (copied handle)
            Int(2),                       // element 1
            Int(4),                       // element 2
            Sized(List { elems: 3 }, 10), // re-marked by the adopt-return
        ]
    );
}

// --- Set ----------------------------------------------------------------

#[test]
fn set_atom_in_direct_list() {
    // set([1, 2], 0, 9) -> [9, 2]; old extent, value, and index become ghost
    assert_eq!(
        values(vec![
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 0),
            Int(9), // new value
            Int(0), // index
            Sized(Set, 0),
        ]),
        [
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 2),
            Int(9),
            Int(0),
            Int(9), // element 0 (replaced)
            Int(2), // element 1 (copied)
            Sized(List { elems: 2 }, 7),
        ]
    );
}

#[test]
fn set_compound_value() {
    // set([1, 2], 1, [3, 4]) -> [1, [3, 4]]; the new value stays put and its
    // handle points down at it — no forward ref can arise.
    assert_eq!(
        values(vec![
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 0),
            Int(3),
            Int(4),
            Sized(List { elems: 2 }, 0),
            Int(1), // index
            Sized(Set, 0),
        ]),
        [
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 2),
            Int(3),
            Int(4),
            Sized(List { elems: 2 }, 2), // the new value, owned inline
            Int(1),
            Int(1),            // element 0 (copied)
            Ref { offset: 3 }, // element 1 -> new value's marker
            Sized(List { elems: 2 }, 9),
        ]
    );
}

#[test]
fn set_in_borrowed_list() {
    // (λx. set(x, 0, 9))([1, 2]) — copy-on-write: the argument list is
    // untouched; the callee returns a modified copy that borrows element 1.
    assert_eq!(
        values(vec![
            Sized(FuncStart, 4),           // 0
            Var { elem: 0 },               // 1
            Int(9),                        // 2
            Int(0),                        // 3
            Sized(Set, 0),                 // 4
            Sized(FuncEnd { args: 1 }, 4), // 5
            Int(1),                        // 6
            Int(2),                        // 7
            Sized(List { elems: 2 }, 0),   // 8
            Sized(Call { args: 1 }, 0),    // 9
        ]),
        [
            Ref { offset: 5 }, // function handle
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 2), // the argument list, unchanged
            Ref { offset: 1 },           // arg handle
            Ref { offset: 2 },           // Var borrow of x
            Int(9),
            Int(0),
            Int(9),                       // element 0 (replaced)
            Int(2),                       // element 1 (copied from the original)
            Sized(List { elems: 2 }, 10), // re-marked by the adopt-return
        ]
    );
}

// --- Get ----------------------------------------------------------------

#[test]
fn get_atom_from_direct_list() {
    // get([1, 2], 0) — the whole extent dies; the atom lands at its base
    assert_eq!(
        values(vec![Int(1), Int(2), Sized(List { elems: 2 }, 0), Int(0), Sized(Get, 0)]),
        [Int(1)]
    );
}

#[test]
fn get_compound_element_through_handle() {
    // (λx. len(x[0]))([[7, 8], 9]) = 2 — the borrowed Get yields a rebased
    // ref to the inner list; Len follows it, so an off-by-anything in the
    // rebase fails loudly here.
    assert_eq!(
        values(vec![
            Sized(FuncStart, 4),           // 0
            Var { elem: 0 },               // 1  x
            Int(0),                        // 2
            Sized(Get, 0),                 // 3  x[0] -> ref to inner list
            Sized(Len, 0),                 // 4
            Sized(FuncEnd { args: 1 }, 4), // 5
            Int(7),                        // 6
            Int(8),                        // 7
            Sized(List { elems: 2 }, 0),   // 8  inner
            Int(9),                        // 9
            Sized(List { elems: 2 }, 0),   // 10 outer
            Sized(Call { args: 1 }, 0),    // 11
        ]),
        [Int(2)]
    );
}

#[test]
fn get_surviving_ref_from_direct_list() {
    // (λx. len(get([x[0], 5], 0)))([[7, 8], 9]) = 2 — the local list dies
    // under Get, but its element 0 borrows data below the dying extent, so
    // the ref survives via the downward rebase (base - target), the only
    // downward move in the VM.
    assert_eq!(
        values(vec![
            Sized(FuncStart, 8),           // 0
            Var { elem: 0 },               // 1  x
            Int(0),                        // 2
            Sized(Get, 0),                 // 3  x[0] -> ref to inner list
            Int(5),                        // 4
            Sized(List { elems: 2 }, 0),   // 5  ys = [x[0], 5], direct
            Int(0),                        // 6
            Sized(Get, 0),                 // 7  get(ys, 0): direct, ref survives
            Sized(Len, 0),                 // 8
            Sized(FuncEnd { args: 1 }, 8), // 9
            Int(7),                        // 10
            Int(8),                        // 11
            Sized(List { elems: 2 }, 0),   // 12 inner
            Int(9),                        // 13
            Sized(List { elems: 2 }, 0),   // 14 outer arg
            Sized(Call { args: 1 }, 0),    // 15
        ]),
        [Int(2)]
    );
}

#[test]
fn get_empty_list_element() {
    // get([[], 5], 0) — an empty list is the one legal 1-slot marker in an
    // element slot; it moves verbatim to the dying extent's base.
    assert_eq!(
        values(vec![
            Sized(List { elems: 0 }, 0),
            Int(5),
            Sized(List { elems: 2 }, 0),
            Int(0),
            Sized(Get, 0),
        ]),
        [Sized(List { elems: 0 }, 0)]
    );
}

// --- closures ----------------------------------------------------------------
//
// A closure is a List whose FIRST element is the code handle, followed by the
// captured values: a frozen call prefix. Call splices the captures (not the
// code) below the call-site args, so Var(0..k) are captures and Var(k..) are
// args; FuncEnd's declared arity counts captures + args. A recursive closure
// simply captures its own code handle.

#[test]
fn closure_call_direct() {
    // [code, 3](4) = 7, closure built and consumed at the call site
    assert_eq!(
        values(vec![
            Sized(FuncStart, 3),           // 0  λ(n, x). n + x
            Var { elem: 0 },               // 1  n (capture)
            Var { elem: 1 },               // 2  x (arg)
            Sized(Bin(BinOp::Add), 0),     // 3
            Sized(FuncEnd { args: 2 }, 3), // 4  1 capture + 1 arg
            Ref { offset: 1 },             // 5  code handle -> 4
            Int(3),                        // 6  capture
            Sized(List { elems: 2 }, 0),   // 7  closure [code, 3]
            Int(4),                        // 8  arg
            Sized(Call { args: 1 }, 0),    // 9
        ]),
        [
            Ref { offset: 6 }, // auto-pushed handle from walking the bracket
            Int(7),            // result, slid down to the frame floor
        ]
    );
}

#[test]
fn countdown_via_closure() {
    // c = [code, code]; c(3) = 0 — a recursive closure captures its own code:
    // Var(0) is the self-capture, recursion rebuilds [Var(0), Var(0)].
    let tape = run(vec![
        Sized(FuncStart, 16),           // 0
        Sized(FuncStart, 1),            // 1  then-arm
        Int(0),                         // 2
        Sized(FuncEnd { args: 0 }, 1),  // 3
        Sized(FuncStart, 7),            // 4  else-arm
        Var { elem: 0 },                // 5  own code (callee elem)
        Var { elem: 0 },                // 6  own code (self-capture)
        Sized(List { elems: 2 }, 0),    // 7  rebuild [code, code]
        Var { elem: 1 },                // 8  n
        Int(1),                         // 9
        Sized(Bin(BinOp::Sub), 0),      // 10
        Sized(Call { args: 1 }, 0),     // 11
        Sized(FuncEnd { args: 0 }, 7),  // 12
        Var { elem: 1 },                // 13
        Int(0),                         // 14
        Sized(Bin(BinOp::Eq), 0),       // 15
        Sized(If, 0),                   // 16
        Sized(FuncEnd { args: 2 }, 16), // 17 1 capture + 1 arg
        Ref { offset: 1 },              // 18 code handle -> 17
        Ref { offset: 2 },              // 19 code handle -> 17
        Sized(List { elems: 2 }, 0),    // 20 closure [code, code]
        Int(3),                         // 21
        Sized(Call { args: 1 }, 0),     // 22
    ]);
    assert_eq!(tape.last(), Some(&Int(0)));
}

#[test]
fn returned_closure_applied() {
    // apply(make_adder(3), 4) = 7 — the closure survives make_adder's return
    // via the adopt-return, is normalized to a handle as apply's argument,
    // and is called through that borrowed handle.
    let tape = run(vec![
        Sized(FuncStart, 3),           // 0  adder code = λ(n, x). n + x
        Var { elem: 0 },               // 1
        Var { elem: 1 },               // 2
        Sized(Bin(BinOp::Add), 0),     // 3
        Sized(FuncEnd { args: 2 }, 3), // 4
        Sized(FuncStart, 3),           // 5  make_adder = λn. [code, n]
        Ref { offset: 2 },             // 6  code handle -> 4
        Var { elem: 0 },               // 7  n
        Sized(List { elems: 2 }, 0),   // 8
        Sized(FuncEnd { args: 1 }, 3), // 9
        Sized(FuncStart, 3),           // 10 apply = λ(g, x). g(x)
        Var { elem: 0 },               // 11
        Var { elem: 1 },               // 12
        Sized(Call { args: 1 }, 0),    // 13
        Sized(FuncEnd { args: 2 }, 3), // 14
        Ref { offset: 1 },             // 15 callee: apply -> 14
        Ref { offset: 7 },             // 16 callee: make_adder -> 9
        Int(3),                        // 17
        Sized(Call { args: 1 }, 0),    // 18 make_adder(3)
        Int(4),                        // 19
        Sized(Call { args: 2 }, 0),    // 20 apply(closure, 4)
    ]);
    assert_eq!(tape.last(), Some(&Int(7)));
}

#[test]
fn closure_arity_mismatch() {
    // [code, 3](4): captures + args = 2, but the code declares 3 — must error
    expect_err(vec![
        Sized(FuncStart, 1),           // 0
        Int(0),                        // 1
        Sized(FuncEnd { args: 3 }, 1), // 2
        Ref { offset: 1 },             // 3  -> 2
        Int(3),                        // 4
        Sized(List { elems: 2 }, 0),   // 5
        Int(4),                        // 6
        Sized(Call { args: 1 }, 0),    // 7
    ]);
}

#[test]
fn closure_without_code() {
    // element 0 must resolve to a FuncEnd
    expect_err(vec![
        Int(5),
        Int(3),
        Sized(List { elems: 2 }, 0),
        Int(4),
        Sized(Call { args: 1 }, 0),
    ]);
}

// --- If ----------------------------------------------------------------

/// λn. if n == 0 { 1 } else { 7 }, called with `n`.
fn if_prog(n: i64) -> Vec<Op> {
    vec![
        Sized(FuncStart, 10), // 0
        Sized(FuncStart, 1),
        Int(1),
        Sized(FuncEnd { args: 0 }, 1), // 1..=3  then-arm
        Sized(FuncStart, 1),
        Int(7),
        Sized(FuncEnd { args: 0 }, 1),  // 4..=6  else-arm
        Var { elem: 0 },                // 7
        Int(0),                         // 8
        Sized(Bin(BinOp::Eq), 0),       // 9
        Sized(If, 0),                   // 10
        Sized(FuncEnd { args: 1 }, 10), // 11
        Int(n),                         // 12
        Sized(Call { args: 1 }, 0),     // 13
    ]
}

#[test]
fn if_selects_then_arm() {
    assert_eq!(values(if_prog(0)), [Int(1)]);
}

#[test]
fn if_selects_else_arm() {
    assert_eq!(values(if_prog(5)), [Int(7)]);
}

#[test]
fn non_tail_if() {
    // λn. n + (if n == 0 { 1 } else { 7 }), called with 5 → 12.
    // The borrow of n for the outer Add is pushed *before* the arms run, so a
    // join return must not truncate below its own floor (the arm handles).
    assert_eq!(
        values(vec![
            Sized(FuncStart, 12), // 0
            Var { elem: 0 },      // 1  n, operand of Add
            Sized(FuncStart, 1),
            Int(1),
            Sized(FuncEnd { args: 0 }, 1), // 2..=4  then-arm
            Sized(FuncStart, 1),
            Int(7),
            Sized(FuncEnd { args: 0 }, 1),  // 5..=7  else-arm
            Var { elem: 0 },                // 8
            Int(0),                         // 9
            Sized(Bin(BinOp::Eq), 0),       // 10
            Sized(If, 0),                   // 11
            Sized(Bin(BinOp::Add), 0),      // 12
            Sized(FuncEnd { args: 1 }, 12), // 13
            Int(5),                         // 14
            Sized(Call { args: 1 }, 0),     // 15
        ]),
        [Int(12)]
    );
}

// --- malformed bytecode must error, never panic --------------------------------

fn expect_err(program: Vec<Op>) {
    let mut vm = Vm::load(program);
    assert!(vm.run().is_err(), "expected an error, got:\n{vm:#?}");
}

#[test]
fn malformed_if_at_stack_bottom() {
    // cond is a program slot after ip; true-arm position underflows
    expect_err(vec![Sized(If, 0), Int(5)]);
}

#[test]
fn malformed_len_through_crafted_ref() {
    // Ref{9} read as the Len operand; target position underflows
    expect_err(vec![Sized(Len, 0), Ref { offset: 9 }]);
}

#[test]
fn malformed_len_of_oversized_marker() {
    // crafted List marker claims more slots than the stack holds
    expect_err(vec![Sized(Len, 0), Sized(List { elems: 2 }, 9)]);
}

#[test]
fn malformed_call_through_crafted_ref() {
    // Ref{9} read as the callee; resolve_slot target underflows
    expect_err(vec![Sized(Call { args: 0 }, 0), Ref { offset: 9 }]);
}

#[test]
fn malformed_call_of_oversized_funcend() {
    // crafted FuncEnd claims a 9-slot body; entry address underflows
    expect_err(vec![Sized(Call { args: 0 }, 0), Sized(FuncEnd { args: 0 }, 9)]);
}

#[test]
fn malformed_call_of_oversized_funcstart() {
    // a FuncStart is not a callable target at all since arity moved to
    // FuncEnd — a plain invalid-function error, no arithmetic reached
    expect_err(vec![Sized(Call { args: 0 }, 0), Sized(FuncStart, 9)]);
}

#[test]
fn malformed_bracket_larger_than_tape() {
    // FuncStart whose extent runs past the end of the program
    expect_err(vec![Sized(FuncStart, 9)]);
}

#[test]
fn malformed_ref_inside_skipped_bracket() {
    // a crafted Ref hidden in a (never-executed) bracket body, borrowed via a
    // Ref instruction, then detonated by Len
    expect_err(vec![
        Sized(FuncStart, 1),
        Ref { offset: 9 },
        Sized(FuncEnd { args: 0 }, 1),
        Ref { offset: 2 },
        Sized(Len, 0),
    ]);
}

// --- recursion ----------------------------------------------------------------

#[test]
fn countdown_recursion() {
    // f = λn. if n == 0 { 0 } else { f(n - 1) }; f(3) — recursion by
    // threading: the function receives itself as an ordinary argument
    // (f_impl(self, n)), so every reference to it is a backwards handle to
    // its FuncEnd and Call needs no FuncStart target.
    assert_eq!(
        values(vec![
            Sized(FuncStart, 15),           // 0  f_impl = λ(self, n)
            Sized(FuncStart, 1),            // 1  then-arm
            Int(0),                         // 2
            Sized(FuncEnd { args: 0 }, 1),  // 3
            Sized(FuncStart, 6),            // 4  else-arm
            Var { elem: 0 },                // 5  self as callee
            Var { elem: 0 },                // 6  self as arg 0
            Var { elem: 1 },                // 7  n
            Int(1),                         // 8
            Sized(Bin(BinOp::Sub), 0),      // 9
            Sized(Call { args: 2 }, 0),     // 10
            Sized(FuncEnd { args: 0 }, 6),  // 11
            Var { elem: 1 },                // 12
            Int(0),                         // 13
            Sized(Bin(BinOp::Eq), 0),       // 14
            Sized(If, 0),                   // 15
            Sized(FuncEnd { args: 2 }, 15), // 16
            Ref { offset: 1 },              // 17 duplicate self handle -> 16
            Int(3),                         // 18
            Sized(Call { args: 2 }, 0),     // 19
        ]),
        [Int(0)]
    );
}

// --- higher-order functions ---------------------------------------------------
//
// map and fold, hand-compiled with threading recursion: the function receives
// itself as arg 0, the worker f flows as an ordinary FuncEnd handle, and list
// access goes through Var handles (Get's O(1) borrow path).

/// Assert the tape's top value is a list whose elements are exactly `expected`.
fn assert_result_list(tape: &[Op], expected: &[Op]) {
    let Some(&Sized(List { elems }, _)) = tape.last() else {
        panic!("expected a list on top, got {:?}", tape.last());
    };
    assert_eq!(elems, expected.len());
    assert_eq!(&tape[tape.len() - 1 - elems..tape.len() - 1], expected);
}

#[test]
fn fold_add_over_list() {
    // fold(add, 0, [1, 2, 3]) = 6
    // fold_impl = λ(self, f, i, acc, xs).
    //     if i == len(xs) { acc } else { self(self, f, i+1, f(acc, xs[i]), xs) }
    let tape = run(vec![
        Sized(FuncStart, 24),           // 0  fold_impl
        Sized(FuncStart, 1),            // 1  then-arm: acc
        Var { elem: 3 },                // 2
        Sized(FuncEnd { args: 0 }, 1),  // 3
        Sized(FuncStart, 14),           // 4  else-arm
        Var { elem: 0 },                // 5  callee: self
        Var { elem: 0 },                // 6  arg0: self
        Var { elem: 1 },                // 7  arg1: f
        Var { elem: 2 },                // 8  arg2: i + 1
        Int(1),                         // 9
        Sized(Bin(BinOp::Add), 0),      // 10
        Var { elem: 1 },                // 11 callee: f
        Var { elem: 3 },                // 12 acc
        Var { elem: 4 },                // 13 xs
        Var { elem: 2 },                // 14 i
        Sized(Get, 0),                  // 15 xs[i]
        Sized(Call { args: 2 }, 0),     // 16 arg3: f(acc, xs[i])
        Var { elem: 4 },                // 17 arg4: xs
        Sized(Call { args: 5 }, 0),     // 18
        Sized(FuncEnd { args: 0 }, 14), // 19
        Var { elem: 2 },                // 20 cond: i == len(xs)
        Var { elem: 4 },                // 21
        Sized(Len, 0),                  // 22
        Sized(Bin(BinOp::Eq), 0),       // 23
        Sized(If, 0),                   // 24
        Sized(FuncEnd { args: 5 }, 24), // 25
        Sized(FuncStart, 3),            // 26 add = λ(a, b). a + b
        Var { elem: 0 },                // 27
        Var { elem: 1 },                // 28
        Sized(Bin(BinOp::Add), 0),      // 29
        Sized(FuncEnd { args: 2 }, 3),  // 30
        Ref { offset: 6 },              // 31 callee: fold_impl (-> 25)
        Ref { offset: 7 },              // 32 self (-> 25)
        Ref { offset: 3 },              // 33 f: add (-> 30)
        Int(0),                         // 34 i
        Int(0),                         // 35 acc
        Int(1),                         // 36 xs...
        Int(2),                         // 37
        Int(3),                         // 38
        Sized(List { elems: 3 }, 0),    // 39
        Sized(Call { args: 5 }, 0),     // 40
    ]);
    assert_eq!(tape.last(), Some(&Int(6)));
}

#[test]
fn map_double_over_list() {
    // map(double, [1, 2, 3]) = [2, 4, 6]
    // map_impl = λ(self, f, i, acc, xs).
    //     if i == len(xs) { push(acc) }    -- fresh copy: returning the borrow
    //                                      -- of acc itself would be the 4-pass
    //                                      -- compaction case; the copy makes
    //                                      -- every return a list-marker return
    //     else { self(self, f, i+1, push(acc, f(xs[i])), xs) }
    let tape = run(vec![
        Sized(FuncStart, 26),           // 0  map_impl
        Sized(FuncStart, 2),            // 1  then-arm: push(acc)
        Var { elem: 3 },                // 2
        Sized(Push { elems: 0 }, 0),    // 3
        Sized(FuncEnd { args: 0 }, 2),  // 4
        Sized(FuncStart, 15),           // 5  else-arm
        Var { elem: 0 },                // 6  callee: self
        Var { elem: 0 },                // 7  arg0: self
        Var { elem: 1 },                // 8  arg1: f
        Var { elem: 2 },                // 9  arg2: i + 1
        Int(1),                         // 10
        Sized(Bin(BinOp::Add), 0),      // 11
        Var { elem: 3 },                // 12 arg3: push(acc, f(xs[i]))
        Var { elem: 1 },                // 13 callee: f
        Var { elem: 4 },                // 14 xs
        Var { elem: 2 },                // 15 i
        Sized(Get, 0),                  // 16 xs[i]
        Sized(Call { args: 1 }, 0),     // 17 f(xs[i])
        Sized(Push { elems: 1 }, 0),    // 18
        Var { elem: 4 },                // 19 arg4: xs
        Sized(Call { args: 5 }, 0),     // 20
        Sized(FuncEnd { args: 0 }, 15), // 21
        Var { elem: 2 },                // 22 cond: i == len(xs)
        Var { elem: 4 },                // 23
        Sized(Len, 0),                  // 24
        Sized(Bin(BinOp::Eq), 0),       // 25
        Sized(If, 0),                   // 26
        Sized(FuncEnd { args: 5 }, 26), // 27
        Sized(FuncStart, 3),            // 28 double = λx. x + x
        Var { elem: 0 },                // 29
        Var { elem: 0 },                // 30
        Sized(Bin(BinOp::Add), 0),      // 31
        Sized(FuncEnd { args: 1 }, 3),  // 32
        Ref { offset: 6 },              // 33 callee: map_impl (-> 27)
        Ref { offset: 7 },              // 34 self (-> 27)
        Ref { offset: 3 },              // 35 f: double (-> 32)
        Int(0),                         // 36 i
        Sized(List { elems: 0 }, 0),    // 37 acc = []
        Int(1),                         // 38 xs...
        Int(2),                         // 39
        Int(3),                         // 40
        Sized(List { elems: 3 }, 0),    // 41
        Sized(Call { args: 5 }, 0),     // 42
    ]);
    assert_result_list(&tape, &[Int(2), Int(4), Int(6)]);
}

// --- compaction ----------------------------------------------------------------
//
// The forced sites (ref-into-frame return, Get's compound extraction) and the
// knob (compact a list return when the frame residue exceeds the value's own
// extent). Layouts here pin the algorithm: per-slot marks, immobile shift
// meta, root re-marked over its ghost.

#[test]
fn empty_list_return_compacts() {
    // (λx. [])(0) — residue 2 > extent 0, so the knob compacts; the root is a
    // bare marker with no elements, the smallest legal mark set.
    assert_eq!(
        values(vec![
            Sized(FuncStart, 1),
            Sized(List { elems: 0 }, 0),
            Sized(FuncEnd { args: 1 }, 1),
            Int(0),
            Sized(Call { args: 1 }, 0),
        ]),
        [Sized(List { elems: 0 }, 0)]
    );
}

#[test]
fn knob_compacts_when_garbage_dominates() {
    // (λx. dead = [9, 9]; [1, 2])(0) — residue 5 > extent 2: the knob picks
    // compaction over adoption and the dead local list is squeezed out.
    assert_eq!(
        values(vec![
            Sized(FuncStart, 6),
            Int(9),
            Int(9),
            Sized(List { elems: 2 }, 0),
            Int(1),
            Int(2),
            Sized(List { elems: 2 }, 0),
            Sized(FuncEnd { args: 1 }, 6),
            Int(0),
            Sized(Call { args: 1 }, 0),
        ]),
        [Int(1), Int(2), Sized(List { elems: 2 }, 2)]
    );
}

#[test]
fn get_compound_element_from_direct_list() {
    // get([[7, 8], 9], 0) — the extracted element is a borrow into the dying
    // extent: the same routine runs with the extent base as the floor, and
    // the caller receives the inner list itself at that base.
    assert_eq!(
        values(vec![
            Int(7),
            Int(8),
            Sized(List { elems: 2 }, 0),
            Int(9),
            Sized(List { elems: 2 }, 0),
            Int(0),
            Sized(Get, 0),
        ]),
        [Int(7), Int(8), Sized(List { elems: 2 }, 2)]
    );
}

#[test]
fn len_of_compound_element_from_direct_list() {
    // len(get([[7, 8], 9], 0)) = 2 — the compacted extraction is a live,
    // walkable value.
    assert_eq!(
        values(vec![
            Int(7),
            Int(8),
            Sized(List { elems: 2 }, 0),
            Int(9),
            Sized(List { elems: 2 }, 0),
            Int(0),
            Sized(Get, 0),
            Sized(Len, 0),
        ]),
        [Int(2)]
    );
}

#[test]
fn root_adopts_ghost_and_shared_child() {
    // (λy. y)((λa. [a, [a, 5]])([7, 8])) — the inner call adopt-returns
    // w = [a, b] with b = [a, 5]; the outer identity return forces the passes.
    // a is a shared child (marked once, both refs to it fixed independently),
    // b survives as ghost below w's element run with its interior ref
    // rewritten (the erratum-2 rule), the junk w adopted from the inner frame
    // is squeezed back out (elements-only marking at the root), and the root
    // marker is re-marked to cover the whole survivor block — without that,
    // a and b would sit outside every extent and the caller's walks misparse.
    assert_eq!(
        values(vec![
            Sized(FuncStart, 1),           // 0  identity
            Var { elem: 0 },               // 1
            Sized(FuncEnd { args: 1 }, 1), // 2
            Sized(FuncStart, 5),           // 3  λa. [a, [a, 5]]
            Var { elem: 0 },               // 4
            Var { elem: 0 },               // 5
            Int(5),                        // 6
            Sized(List { elems: 2 }, 0),   // 7  b = [a, 5]
            Sized(List { elems: 2 }, 0),   // 8  w = [a, b]
            Sized(FuncEnd { args: 1 }, 5), // 9
            Int(7),                        // 10
            Int(8),                        // 11
            Sized(List { elems: 2 }, 0),   // 12 arg [7, 8]
            Sized(Call { args: 1 }, 0),    // 13 inner call (callee: λa handle)
            Sized(Call { args: 1 }, 0),    // 14 outer call (callee: identity handle)
        ]),
        [
            Int(7),
            Int(8),
            Sized(List { elems: 2 }, 2), // a — ghost, shared
            Ref { offset: 1 },           // b[0] -> a
            Int(5),
            Sized(List { elems: 2 }, 2), // b — ghost
            Ref { offset: 4 },           // w[0] -> a
            Ref { offset: 2 },           // w[1] -> b
            Sized(List { elems: 2 }, 8), // w — root, re-marked over the ghost
        ]
    );
}

#[test]
fn transitive_mark_through_garbage_parent() {
    // (λx. [x[1]])([3, [2, [99]], 4]) — the argument B is garbage, but its
    // element A (borrowed out via Get) is live: the mark pass must walk B's
    // extent slot by slot instead of skipping it, so A's whole extent
    // (including the inline [99]) survives while B's marker, its other
    // elements, and its handles are squeezed. The erratum-1 shape.
    assert_eq!(
        values(vec![
            Sized(FuncStart, 4),           // 0
            Var { elem: 0 },               // 1
            Int(1),                        // 2
            Sized(Get, 0),                 // 3  x[1] -> borrow of A
            Sized(List { elems: 1 }, 0),   // 4  root [->A]
            Sized(FuncEnd { args: 1 }, 4), // 5
            Int(3),                        // 6
            Int(2),                        // 7
            Int(99),                       // 8
            Sized(List { elems: 1 }, 0),   // 9  Z = [99]
            Sized(List { elems: 2 }, 0),   // 10 A = [2, Z]
            Int(4),                        // 11
            Sized(List { elems: 3 }, 0),   // 12 B = [3, A, 4]
            Sized(Call { args: 1 }, 0),    // 13
        ]),
        [
            Int(2), // A's dead original operand (interior marking is whole-extent)
            Int(99),
            Sized(List { elems: 1 }, 1), // Z
            Int(2),                      // A[0]
            Ref { offset: 2 },           // A[1] -> Z
            Sized(List { elems: 2 }, 5), // A
            Ref { offset: 1 },           // root[0] -> A
            Sized(List { elems: 1 }, 7), // root — re-marked
        ]
    );
}

#[test]
fn stale_shift_below_floor() {
    // apply(make([3, 3])) with make = λn. [code, n] and code = λ(cap, x).
    // [cap, x]: make's return compacts (knob), stamping nonzero shift meta
    // into the closure's slots — including the capture list's final position.
    // The closure is then called through a borrowed handle, so its capture
    // sits BELOW that call's floor, and the body's return compacts with a
    // marked ref to it. The ref fix must treat below-floor targets as
    // unmoved (shift 0); reading the stale stamp instead lands the ref one
    // slot low, inside the capture's elements.
    assert_eq!(
        values(vec![
            Sized(FuncStart, 3),           // 0  code = λ(cap, x). [cap, x]
            Var { elem: 0 },               // 1
            Var { elem: 1 },               // 2
            Sized(List { elems: 2 }, 0),   // 3
            Sized(FuncEnd { args: 2 }, 3), // 4
            Sized(FuncStart, 3),           // 5  apply = λg. g(9)
            Var { elem: 0 },               // 6
            Int(9),                        // 7
            Sized(Call { args: 1 }, 0),    // 8
            Sized(FuncEnd { args: 1 }, 3), // 9
            Sized(FuncStart, 3),           // 10 make = λn. [code, n]
            Ref { offset: 7 },             // 11 code handle -> 4
            Var { elem: 0 },               // 12
            Sized(List { elems: 2 }, 0),   // 13
            Sized(FuncEnd { args: 1 }, 3), // 14
            Int(3),                        // 15
            Int(3),                        // 16
            Sized(List { elems: 2 }, 0),   // 17 n = [3, 3]
            Sized(Call { args: 1 }, 0),    // 18 make(n) (callee: make handle)
            Sized(Call { args: 1 }, 0),    // 19 apply(closure) (callee: apply handle)
        ]),
        [
            Ref { offset: 16 }, // leftover handle from walking code's bracket
            Int(3),
            Int(3),
            Sized(List { elems: 2 }, 2), // the capture list, ghost of the result
            Ref { offset: 1 }, // result[0] -> capture list (one too low if stale shift is read)
            Int(9),            // result[1]
            Sized(List { elems: 2 }, 5), // result — root, re-marked
        ]
    );
}
