//! Lisp-style cons-list VM for comparison.
//!
//! Uses the same Op instruction set as the flat VM. All compound data is
//! represented as cons cells: Cons(head, tail). The chain is stored in
//! reverse logical order (last element at head), so that Push/Pop operate
//! at the logical end in O(1), matching the flat VM's semantics.
//!
//! Get(k) translates the logical index to a physical chain position,
//! which requires knowing the length: O(n) per access.
//!
//! Each value occupies exactly 1 stack slot, so Copy(offset) and
//! Call(arg_count) use slot counts that equal value counts.

use std::rc::Rc;

use crate::Op;

#[derive(Debug, Clone)]
pub enum Val {
    Int(i64),
    Str(usize),
    Func(usize),
    Cons(Rc<(Val, Val)>),
    Nil,
}

fn cons_get(val: &Val, mut index: usize) -> Val {
    let mut current = val;
    loop {
        match current {
            Val::Cons(pair) => {
                if index == 0 {
                    return pair.0.clone();
                }
                index -= 1;
                current = &pair.1;
            }
            _ => panic!("Cons list index out of bounds"),
        }
    }
}

fn cons_set(val: Val, index: usize, new_val: Val) -> Val {
    match val {
        Val::Cons(pair) => {
            if index == 0 {
                Val::Cons(Rc::new((new_val, pair.1.clone())))
            } else {
                Val::Cons(Rc::new((
                    pair.0.clone(),
                    cons_set(pair.1.clone(), index - 1, new_val),
                )))
            }
        }
        _ => panic!("Cons list index out of bounds in Set"),
    }
}

fn cons_len(val: &Val) -> usize {
    let mut count = 0;
    let mut current = val;
    loop {
        match current {
            Val::Cons(pair) => {
                count += 1;
                current = &pair.1;
            }
            _ => return count,
        }
    }
}

/// Collect all elements from a reversed cons chain into logical order.
fn cons_to_vec(val: &Val) -> Vec<Val> {
    let mut elems = Vec::new();
    let mut current = val;
    while let Val::Cons(pair) = current {
        elems.push(pair.0.clone());
        current = &pair.1;
    }
    elems.reverse();
    elems
}

struct CallFrame {
    frame_pointer: usize,
    ret_address: usize,
}

pub struct Vm {
    ip: usize,
    ops: Vec<Op>,
    stack: Vec<Val>,
    call_frames: Vec<CallFrame>,
}

impl Vm {
    pub fn new(ops: Vec<Op>) -> Self {
        Self::with_ip(ops, 0)
    }

    pub fn with_ip(ops: Vec<Op>, ip: usize) -> Self {
        Vm {
            ip,
            ops,
            stack: Vec::new(),
            call_frames: Vec::new(),
        }
    }

    pub fn run(mut self) -> Vec<Val> {
        while let Some(&op) = self.ops.get(self.ip) {
            self.run_op(op);
        }
        self.stack
    }

    fn run_op(&mut self, op: Op) {
        self.ip += 1;
        match op {
            Op::PushInt(i) => self.stack.push(Val::Int(i)),
            Op::PushStr(s) => self.stack.push(Val::Str(s)),
            Op::PushFunc(f) => self.stack.push(Val::Func(f)),

            Op::MakeList(elems) => {
                // Build the chain in reverse: last logical element at head.
                // Stack elements are in logical order [e0, e1, ..., e_{n-1}].
                // Iterating forward and consing builds the reversed chain.
                let start = self.stack.len() - elems;
                let elements: Vec<Val> = self.stack.drain(start..).collect();
                let mut list = Val::Nil;
                for elem in elements.into_iter() {
                    list = Val::Cons(Rc::new((elem, list)));
                }
                self.stack.push(list);
            }

            Op::Copy(offset) => {
                let pos = self.stack.len() - 1 - offset;
                self.stack.push(self.stack[pos].clone());
            }

            Op::Get(index) => {
                // Logical index k maps to physical position n-1-k in the
                // reversed chain.
                let top = self.stack.pop().unwrap();
                let n = cons_len(&top);
                self.stack.push(cons_get(&top, n - 1 - index));
            }

            Op::Set(index) => {
                let new_val = self.stack.pop().unwrap();
                let target = self.stack.pop().unwrap();
                let n = cons_len(&target);
                self.stack.push(cons_set(target, n - 1 - index, new_val));
            }

            Op::Push => {
                // Cons onto head = append at logical end. O(1).
                let elem = self.stack.pop().unwrap();
                let target = self.stack.pop().unwrap();
                self.stack.push(Val::Cons(Rc::new((elem, target))));
            }

            Op::Pop => {
                // Take head = remove from logical end. O(1).
                let target = self.stack.pop().unwrap();
                match target {
                    Val::Cons(pair) => {
                        self.stack.push(pair.1.clone());
                        self.stack.push(pair.0.clone());
                    }
                    other => panic!("Pop requires Cons, got {other:?}"),
                }
            }

            Op::Call(arg_count) => {
                let func = self.stack.pop().unwrap();
                match func {
                    Val::Func(code_pointer) => {
                        let frame_pointer = self.stack.len() - arg_count;
                        self.call_frames.push(CallFrame {
                            frame_pointer,
                            ret_address: self.ip,
                        });
                        self.ip = code_pointer;
                    }
                    other => panic!("Not a function: {other:?}"),
                }
            }

            Op::Return => {
                let frame = self.call_frames.pop().unwrap();
                self.ip = frame.ret_address;
                let ret_val = if self.stack.len() > frame.frame_pointer {
                    Some(self.stack.pop().unwrap())
                } else {
                    None
                };
                self.stack.truncate(frame.frame_pointer);
                if let Some(v) = ret_val {
                    self.stack.push(v);
                }
            }

            Op::If { if_true, if_false } => {
                let b = self.stack.pop().unwrap();
                let a = self.stack.pop().unwrap();
                self.call_frames.push(CallFrame {
                    frame_pointer: self.stack.len(),
                    ret_address: self.ip,
                });
                match (a, b) {
                    (Val::Int(a), Val::Int(b)) => {
                        self.ip = if a == b { if_true } else { if_false };
                    }
                    (Val::Str(a), Val::Str(b)) => {
                        self.ip = if a == b { if_true } else { if_false };
                    }
                    (a, b) => panic!("Cannot compare {a:?} and {b:?}"),
                }
            }

            Op::Unpack { elems, if_true, if_false } => {
                let top = self.stack.pop().unwrap();
                let actual_elems = cons_len(&top);
                if actual_elems != elems {
                    self.stack.push(top);
                    self.call_frames.push(CallFrame {
                        frame_pointer: self.stack.len(),
                        ret_address: self.ip,
                    });
                    self.ip = if_false;
                } else {
                    self.call_frames.push(CallFrame {
                        frame_pointer: self.stack.len(),
                        ret_address: self.ip,
                    });
                    // Push elements in logical order (e0, e1, ..., e_{n-1}).
                    let logical = cons_to_vec(&top);
                    for elem in logical {
                        self.stack.push(elem);
                    }
                    self.ip = if_true;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Op;

    #[test]
    fn test_make_list_and_get() {
        let vm = Vm::new(vec![
            Op::PushInt(1),
            Op::PushInt(2),
            Op::PushInt(3),
            Op::MakeList(3),
            Op::Get(0),
        ]);
        let stack = vm.run();
        assert_eq!(stack.len(), 1);
        assert!(matches!(&stack[0], Val::Int(1)));
    }

    #[test]
    fn test_call_return() {
        let vm = Vm::with_ip(
            vec![Op::PushInt(99), Op::Return, Op::PushFunc(0), Op::Call(0)],
            2,
        );
        let stack = vm.run();
        assert_eq!(stack.len(), 1);
        assert!(matches!(&stack[0], Val::Int(99)));
    }

    #[test]
    fn test_copy_shares_rc() {
        let vm = Vm::new(vec![
            Op::PushInt(1),
            Op::PushInt(2),
            Op::MakeList(2),
            Op::Copy(0),
        ]);
        let stack = vm.run();
        assert_eq!(stack.len(), 2);
        match (&stack[0], &stack[1]) {
            (Val::Cons(a), Val::Cons(b)) => assert!(Rc::ptr_eq(a, b)),
            _ => panic!("Expected two cons lists"),
        }
    }

    #[test]
    fn test_push_pop() {
        // Push appends at logical end, Pop removes from logical end.
        let vm = Vm::new(vec![
            Op::MakeList(0),
            Op::PushInt(1),
            Op::Push,
            Op::PushInt(2),
            Op::Push,
            Op::Pop,
        ]);
        let stack = vm.run();
        assert_eq!(stack.len(), 2);
        // Pop removes last pushed = 2
        assert!(matches!(&stack[1], Val::Int(2)));
    }

    #[test]
    fn test_set() {
        let vm = Vm::new(vec![
            Op::PushInt(10),
            Op::PushInt(20),
            Op::MakeList(2),
            Op::PushInt(99),
            Op::Set(0),
        ]);
        let stack = vm.run();
        assert_eq!(stack.len(), 1);
        // Verify via Get that element 0 is now 99
        let vm2 = Vm::new(vec![
            Op::PushInt(10),
            Op::PushInt(20),
            Op::MakeList(2),
            Op::PushInt(99),
            Op::Set(0),
            Op::Get(0),
        ]);
        let stack2 = vm2.run();
        assert!(matches!(&stack2[0], Val::Int(99)));
    }

    #[test]
    fn test_get_index() {
        let vm = Vm::new(vec![
            Op::PushInt(10),
            Op::PushInt(20),
            Op::PushInt(30),
            Op::MakeList(3),
            Op::Get(1),
        ]);
        let stack = vm.run();
        assert_eq!(stack.len(), 1);
        assert!(matches!(&stack[0], Val::Int(20)));
    }

    #[test]
    fn test_unpack() {
        let vm = Vm::with_ip(
            vec![
                Op::Return,  // 0: if_true
                Op::Return,  // 1: if_false
                Op::PushInt(10),
                Op::PushInt(20),
                Op::MakeList(2),
                Op::Unpack { elems: 2, if_true: 0, if_false: 1 },
            ],
            2,
        );
        let stack = vm.run();
        // Unpack pushes in logical order: 10 then 20. Return keeps top = 20.
        assert!(matches!(&stack[stack.len() - 1], Val::Int(20)));
    }

    #[test]
    fn test_function_return_compound() {
        let vm = Vm::with_ip(
            vec![
                Op::PushInt(1),
                Op::PushInt(2),
                Op::MakeList(2),
                Op::Return,
                Op::PushFunc(0),
                Op::Call(0),
            ],
            4,
        );
        let stack = vm.run();
        assert_eq!(stack.len(), 1);
        // Get(0) on the returned list should give 1.
        let vm2 = Vm::with_ip(
            vec![
                Op::PushInt(1),
                Op::PushInt(2),
                Op::MakeList(2),
                Op::Return,
                Op::PushFunc(0),
                Op::Call(0),
                Op::Get(0),
            ],
            4,
        );
        let stack2 = vm2.run();
        assert!(matches!(&stack2[0], Val::Int(1)));
    }
}
