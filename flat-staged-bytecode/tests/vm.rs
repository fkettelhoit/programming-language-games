use SizedSlot::*;
use Slot::*;
use flat_staged_bytecode::{BinSlot, SizedSlot, Slot, Vm};

fn run(program: Vec<Slot>) -> Vec<Slot> {
    let mut vm = Vm::load(program);
    if let Err(e) = vm.run() {
        panic!("VM error: {e}\n{vm:#?}");
    }
    vm.stack
}

/// Run and return only the working region (everything above the program prefix).
fn values(program: Vec<Slot>) -> Vec<Slot> {
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
    assert_eq!(values(vec![Int(40), Int(2), Sized(Bin(BinSlot::Add), 0)]), [Int(42)]);
    assert_eq!(values(vec![Int(7), Int(2), Sized(Bin(BinSlot::Sub), 0)]), [Int(5)]);
    assert_eq!(values(vec![Int(6), Int(7), Sized(Bin(BinSlot::Mul), 0)]), [Int(42)]);
    assert_eq!(values(vec![Int(3), Int(3), Sized(Bin(BinSlot::Eq), 0)]), [Int(1)]);
    assert_eq!(values(vec![Int(3), Int(4), Sized(Bin(BinSlot::Eq), 0)]), [Int(0)]);
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
#[ignore = "returning a borrow of frame-local data requires the 4-pass compaction"]
fn call_with_list_arg() {
    // (λx. x)([1, 2]) — the returned borrow points into the dying frame; the
    // expected layout will be written together with the compaction.
    run(vec![
        Sized(FuncStart, 1),
        Var { elem: 0 },
        Sized(FuncEnd { args: 1 }, 1),
        Int(1),
        Int(2),
        Sized(List { elems: 2 }, 0),
        Sized(Call { args: 1 }, 0),
    ]);
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

// --- If ----------------------------------------------------------------

/// λn. if n == 0 { 1 } else { 7 }, called with `n`.
fn if_prog(n: i64) -> Vec<Slot> {
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
        Sized(Bin(BinSlot::Eq), 0),     // 9
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
            Sized(Bin(BinSlot::Eq), 0),     // 10
            Sized(If, 0),                   // 11
            Sized(Bin(BinSlot::Add), 0),    // 12
            Sized(FuncEnd { args: 1 }, 12), // 13
            Int(5),                         // 14
            Sized(Call { args: 1 }, 0),     // 15
        ]),
        [Int(12)]
    );
}

// --- malformed bytecode must error, never panic --------------------------------

fn expect_err(program: Vec<Slot>) {
    let mut vm = Vm::load(program);
    assert!(vm.run().is_err(), "expected an error, got:\n{vm:#?}");
}

#[test]
#[ignore = "hardening deferred until the experiment is built out"]
fn malformed_if_at_stack_bottom() {
    // cond is a program slot after ip; true-arm position underflows
    expect_err(vec![Sized(If, 0), Int(5)]);
}

#[test]
#[ignore = "hardening deferred until the experiment is built out"]
fn malformed_len_through_crafted_ref() {
    // Ref{9} read as the Len operand; target position underflows
    expect_err(vec![Sized(Len, 0), Ref { offset: 9 }]);
}

#[test]
#[ignore = "hardening deferred until the experiment is built out"]
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
#[ignore = "hardening deferred until the experiment is built out"]
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
#[ignore = "hardening deferred until the experiment is built out"]
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
            Sized(Bin(BinSlot::Sub), 0),    // 9
            Sized(Call { args: 2 }, 0),     // 10
            Sized(FuncEnd { args: 0 }, 6),  // 11
            Var { elem: 1 },                // 12
            Int(0),                         // 13
            Sized(Bin(BinSlot::Eq), 0),     // 14
            Sized(If, 0),                   // 15
            Sized(FuncEnd { args: 2 }, 15), // 16
            Ref { offset: 1 },              // 17 duplicate self handle -> 16
            Int(3),                         // 18
            Sized(Call { args: 2 }, 0),     // 19
        ]),
        [Int(0)]
    );
}
