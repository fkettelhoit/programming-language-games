pub mod traditional;

#[derive(Debug, Clone)]
pub enum Val {
    Int(i64),
    Str(usize),
    Func(usize),
    /// A list of `elems` elements (each exactly 1 stack slot), preceded by
    /// `adopted` slots of adopted child data. Total stack footprint =
    /// `elems + adopted + 1`.
    List { elems: usize, adopted: usize },
    /// Reference to a List marker position on the stack.
    Ref(usize),
}

#[derive(Debug, Clone, Copy)]
pub enum Op {
    PushInt(i64),
    PushStr(usize),
    PushFunc(usize),
    /// Consume the top `n` stack slots as elements (each must be 1 slot:
    /// Int, Str, Func, or Ref). Computes `adopted` from Refs pointing into
    /// the zone immediately below the element area.
    MakeList(usize),
    Copy(usize),
    Get(usize),
    Set(usize),
    Push,
    Pop,
    Call(usize),
    Return,
    If { if_true: usize, if_false: usize },
    Unpack { elems: usize, if_true: usize, if_false: usize },
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

/// Returns the full extent (number of stack slots) of the value whose marker
/// is at `pos`.
fn size_at(stack: &[Val], pos: usize) -> usize {
    match &stack[pos] {
        Val::List { elems, adopted } => elems + adopted + 1,
        _ => 1,
    }
}

/// Compute the `adopted` size for a new List whose `n` element slots are
/// at `stack[elem_start..elem_start + n]`. Adopted data is the contiguous
/// span below elem_start reachable via Refs in the elements.
fn compute_adopted(stack: &[Val], elem_start: usize, n: usize) -> usize {
    let mut lowest = elem_start;
    for i in elem_start..elem_start + n {
        if let Val::Ref(target) = &stack[i] {
            if *target < elem_start {
                let base = *target + 1 - size_at(stack, *target);
                if base < lowest {
                    lowest = base;
                }
            }
        }
    }
    elem_start - lowest
}

/// Recompute `adopted` for a List marker at `marker_pos` by scanning its
/// element slots for Refs and finding the lowest target.
fn recompute_adopted(stack: &[Val], marker_pos: usize, elems: usize) -> usize {
    let elem_start = marker_pos - elems;
    compute_adopted(stack, elem_start, elems)
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

    fn run_op(&mut self, op: Op) {
        self.ip += 1;
        match op {
            Op::PushInt(i) => self.stack.push(Val::Int(i)),
            Op::PushStr(s) => self.stack.push(Val::Str(s)),
            Op::PushFunc(f) => self.stack.push(Val::Func(f)),

            Op::MakeList(n) => {
                let elem_start = self.stack.len() - n;
                let adopted = compute_adopted(&self.stack, elem_start, n);
                self.stack.push(Val::List { elems: n, adopted });
            }

            Op::Copy(offset) => {
                let pos = self.stack.len() - 1 - offset;
                match &self.stack[pos] {
                    Val::List { elems, .. } if *elems > 0 => {
                        self.stack.push(Val::Ref(pos));
                    }
                    Val::Ref(target) => {
                        self.stack.push(Val::Ref(*target));
                    }
                    other => {
                        self.stack.push(other.clone());
                    }
                }
            }

            Op::Get(index) => self.do_get(index),
            Op::Set(index) => self.do_set(index),
            Op::Push => self.do_push(),
            Op::Pop => self.do_pop(),

            Op::Call(arg_slots) => {
                let func = self.stack.pop().unwrap();
                match func {
                    Val::Func(code_pointer) => {
                        let frame_pointer = self.stack.len() - arg_slots;
                        self.call_frames.push(CallFrame {
                            frame_pointer,
                            ret_address: self.ip,
                        });
                        self.ip = code_pointer;
                    }
                    other => panic!("Not a function: {other:?}"),
                }
            }

            Op::Return => self.do_return(),

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
                self.do_unpack(elems, if_true, if_false);
            }
        }
    }

    /// Get on a direct List is destructive: it consumes the entire list
    /// (including adopted data) and leaves only the extracted element.
    /// Use Copy first to get a Ref if you need multiple accesses.
    fn do_get(&mut self, index: usize) {
        let top = self.stack.pop().unwrap();
        match top {
            Val::List { elems, adopted, .. } => {
                let marker_pos = self.stack.len();
                let elem_pos = marker_pos - elems + index;
                let val = self.stack[elem_pos].clone();
                self.stack.truncate(marker_pos - elems - adopted);
                self.stack.push(val);
            }
            Val::Ref(target) => {
                match &self.stack[target] {
                    Val::List { elems, .. } => {
                        let elem_pos = target - elems + index;
                        let val = self.stack[elem_pos].clone();
                        self.stack.push(val);
                    }
                    _ => panic!("Ref target is not a List"),
                }
            }
            other => panic!("Cannot Get from {other:?}"),
        }
    }

    fn do_set(&mut self, index: usize) {
        // Stack: [..., target, new_value]
        let new_val = self.stack.pop().unwrap();
        let target = self.stack.pop().unwrap();
        match target {
            Val::List { elems, adopted } => {
                let marker_pos = self.stack.len();
                let elem_start = marker_pos - elems;
                let elem_pos = elem_start + index;
                self.stack[elem_pos] = new_val;
                // adopted can only grow (it's an upper bound). Check if the
                // new value is a Ref that extends the span.
                let new_adopted = match &self.stack[elem_pos] {
                    Val::Ref(target) if *target < elem_start => {
                        let base = *target + 1 - size_at(&self.stack, *target);
                        adopted.max(elem_start - base)
                    }
                    _ => adopted,
                };
                self.stack.push(Val::List { elems, adopted: new_adopted });
            }
            Val::Ref(ref_target) => {
                // Mutable value semantics: deep-copy the referenced list
                // into a new direct list, then mutate the copy. The
                // original is untouched, so other Refs still see old data.
                let elems = match &self.stack[ref_target] {
                    Val::List { elems, .. } => *elems,
                    _ => panic!("Ref target is not a List"),
                };
                let elem_start = ref_target - elems;
                for i in 0..elems {
                    self.stack.push(self.stack[elem_start + i].clone());
                }
                // Mutate the element in the copy
                let copy_elem_start = self.stack.len() - elems;
                self.stack[copy_elem_start + index] = new_val;
                let adopted = compute_adopted(&self.stack, copy_elem_start, elems);
                self.stack.push(Val::List { elems, adopted });
            }
            other => panic!("Cannot Set on {other:?}"),
        }
    }

    fn do_push(&mut self) {
        // Stack: [..., list, new_element]
        let new_val = self.stack.pop().unwrap();
        let target = self.stack.pop().unwrap();
        match target {
            Val::List { elems, adopted } => {
                // The new element goes where the marker was. The marker moves up.
                // adopted only grows if the new element is a Ref below the element area.
                let elem_start = self.stack.len() - elems;
                let new_adopted = match &new_val {
                    Val::Ref(target) if *target < elem_start => {
                        let base = *target + 1 - size_at(&self.stack, *target);
                        let span = elem_start - base;
                        adopted.max(span)
                    }
                    _ => adopted,
                };
                self.stack.push(new_val);
                self.stack.push(Val::List { elems: elems + 1, adopted: new_adopted });
            }
            other => panic!("Push requires List, got {other:?}"),
        }
    }

    fn do_pop(&mut self) {
        // Pop last element from list. Pushes shortened list, then element.
        let target = self.stack.pop().unwrap();
        match target {
            Val::List { elems, adopted } => {
                assert!(elems > 0, "Pop: empty list");
                let marker_pos = self.stack.len();
                let last_elem_pos = marker_pos - 1;
                let elem = self.stack[last_elem_pos].clone();
                self.stack.truncate(last_elem_pos);
                // adopted is an upper bound — safe to keep as-is even if the
                // popped element was the one that determined the span. Compaction
                // on return will tighten it if needed.
                let new_adopted = if elems > 1 { adopted } else { 0 };
                self.stack.push(Val::List { elems: elems - 1, adopted: new_adopted });
                self.stack.push(elem);
            }
            other => panic!("Pop requires List, got {other:?}"),
        }
    }

    fn do_unpack(&mut self, expected_elems: usize, if_true: usize, if_false: usize) {
        let top = self.stack.pop().unwrap();

        let (elems, direct) = match &top {
            Val::List { elems, .. } => (*elems, true),
            Val::Ref(target) => match &self.stack[*target] {
                Val::List { elems, .. } => (*elems, false),
                _ => panic!("Ref target is not a List"),
            },
            _ => {
                self.stack.push(top);
                self.call_frames.push(CallFrame {
                    frame_pointer: self.stack.len(),
                    ret_address: self.ip,
                });
                self.ip = if_false;
                return;
            }
        };

        if elems != expected_elems {
            self.stack.push(top);
            self.call_frames.push(CallFrame {
                frame_pointer: self.stack.len(),
                ret_address: self.ip,
            });
            self.ip = if_false;
            return;
        }

        if direct {
            // Direct list: elements are already on the stack, preceded
            // by adopted data. Leave everything in place — elements may
            // contain Refs into the adopted zone. The adopted data
            // becomes part of the new call frame and will be cleaned up
            // by compaction when the if_true branch returns.
            if let Val::List { elems, adopted } = top {
                let marker_pos = self.stack.len();
                let elem_start = marker_pos - elems;
                let adopted_start = elem_start - adopted;
                self.call_frames.push(CallFrame {
                    frame_pointer: adopted_start,
                    ret_address: self.ip,
                });
            }
        } else {
            // Ref: copy elements from the referenced list
            if let Val::Ref(target) = top {
                let (elems, _adopted) = match &self.stack[target] {
                    Val::List { elems, adopted } => (*elems, *adopted),
                    _ => unreachable!(),
                };
                self.call_frames.push(CallFrame {
                    frame_pointer: self.stack.len(),
                    ret_address: self.ip,
                });
                let elem_start = target - elems;
                for i in 0..elems {
                    self.stack.push(self.stack[elem_start + i].clone());
                }
            }
        }
        self.ip = if_true;
    }

    /// Compute the "narrow" size of the return value: just the element slots +
    /// marker for a List, or 1 for an atomic value. This excludes adopted data,
    /// which is treated as part of the threatened area during return.
    fn narrow_size(stack: &[Val], pos: usize) -> usize {
        match &stack[pos] {
            Val::List { elems, .. } => elems + 1,
            _ => 1,
        }
    }

    fn do_return(&mut self) {
        let CallFrame { frame_pointer, ret_address } = self.call_frames.pop().unwrap();
        self.ip = ret_address;

        if self.stack.len() <= frame_pointer {
            self.stack.truncate(frame_pointer);
            return;
        }

        let ret_marker = self.stack.len() - 1;
        let ret_size = Self::narrow_size(&self.stack, ret_marker);
        let ret_start = self.stack.len() - ret_size;

        // If the return value is a bare Ref, dereference it.
        if ret_size == 1 {
            if let Val::Ref(target) = self.stack[ret_marker] {
                if target < frame_pointer {
                    // Ref to safe space: keep as-is.
                    self.stack[frame_pointer] = Val::Ref(target);
                    self.stack.truncate(frame_pointer + 1);
                    return;
                }
                // Ref into threatened area: treat target list as the return
                // value. Only compact if that list has refs deeper into the
                // threatened area; otherwise just move it down.
                let target_narrow = Self::narrow_size(&self.stack, target);
                let new_ret_start = target + 1 - target_narrow;
                self.stack.truncate(target + 1);

                if new_ret_start <= frame_pointer {
                    return;
                }

                let needs_compact = (new_ret_start..self.stack.len()).any(|i| {
                    if let Val::Ref(t) = &self.stack[i] {
                        *t >= frame_pointer && *t < new_ret_start
                    } else {
                        false
                    }
                });
                if needs_compact {
                    return self.do_return_compact(
                        frame_pointer, new_ret_start, target_narrow,
                    );
                }
                // Simple move.
                for i in 0..target_narrow {
                    self.stack[frame_pointer + i] =
                        self.stack[new_ret_start + i].clone();
                }
                self.stack.truncate(frame_pointer + target_narrow);
                return;
            }
        }

        if ret_start <= frame_pointer {
            // No threatened area
            return;
        }

        // Quick check: any Refs into threatened area?
        let has_threatened_refs = (ret_start..self.stack.len()).any(|i| {
            if let Val::Ref(target) = &self.stack[i] {
                *target >= frame_pointer && *target < ret_start
            } else {
                false
            }
        });

        if !has_threatened_refs {
            // Simple case: move return value down and truncate
            for i in 0..ret_size {
                self.stack[frame_pointer + i] = self.stack[ret_start + i].clone();
            }
            self.stack.truncate(frame_pointer + ret_size);
        } else {
            self.do_return_compact(frame_pointer, ret_start, ret_size);
        }
    }

    fn do_return_compact(&mut self, frame_pointer: usize, ret_start: usize, ret_size: usize) {
        // 4-pass mark-and-compact
        const MARK_BIT: usize = 1 << (usize::BITS - 1);

        // === Pass 1: Mark (top to bottom) ===
        // Mark reachable Lists by setting MARK_BIT on their `adopted` field.
        // Transitivity: structurally (via inside_floor) and via Refs.
        let mut inside_floor = ret_start;
        let mut i = self.stack.len();
        while i > frame_pointer {
            i -= 1;
            let slot = self.stack[i].clone();
            match slot {
                Val::Ref(target)
                    if target >= frame_pointer
                        && target < ret_start
                        && (i >= ret_start || i >= inside_floor) =>
                {
                    if let Val::List { adopted, .. } = &mut self.stack[target] {
                        *adopted |= MARK_BIT;
                    } else {
                        panic!("Ref target is not a List");
                    }
                }
                Val::List { elems, adopted } if i < ret_start => {
                    if adopted & MARK_BIT != 0 {
                        let orig_adopted = adopted & !MARK_BIT;
                        let extent = elems + orig_adopted;
                        inside_floor = inside_floor.min(i - extent);
                    } else if i >= inside_floor {
                        if let Val::List { adopted: a, .. } = &mut self.stack[i] {
                            *a |= MARK_BIT;
                        }
                        inside_floor = inside_floor.min(i - elems - adopted);
                    } else {
                        // Garbage: keep walking slot by slot. We cannot skip
                        // past the adopted zone because it may contain child
                        // lists that were already marked reachable by a
                        // direct Ref from the return value.
                    }
                }
                _ => {}
            }
        }

        // === Pass 2: Compute gaps (bottom to top) ===
        let mut gap = 0usize;
        let mut i = frame_pointer;
        while i < ret_start {
            if let Val::List { elems, adopted } = &mut self.stack[i] {
                if *adopted & MARK_BIT != 0 {
                    *adopted = gap;
                } else {
                    gap += *elems + *adopted + 1;
                    *adopted = usize::MAX;
                }
            }
            i += 1;
        }

        // === Pass 3: Fix refs (walk threatened area + return value) ===
        // Refs inside reachable data in the threatened area also need
        // fixing — their targets may shift during compaction.
        for i in frame_pointer..self.stack.len() {
            if let Val::Ref(target) = &self.stack[i] {
                let target = *target;
                if target >= frame_pointer && target < ret_start {
                    let gap = match &self.stack[target] {
                        Val::List { adopted, .. } => *adopted,
                        _ => panic!("Ref target is not a List"),
                    };
                    self.stack[i] = Val::Ref(target - gap);
                }
            }
        }

        // === Pass 4: Compact (bottom to top) ===
        let mut write_pos = frame_pointer;
        let mut i = frame_pointer;
        while i < ret_start {
            match &self.stack[i] {
                Val::List { elems, adopted } => {
                    let elems = *elems;
                    let stored = *adopted;
                    if stored != usize::MAX {
                        // Reachable: recompute adopted from elements at write_pos - elems
                        let new_adopted = recompute_adopted(&self.stack, write_pos, elems);
                        self.stack[write_pos] = Val::List { elems, adopted: new_adopted };
                        write_pos += 1;
                    } else {
                        // Garbage: roll back write_pos past eagerly copied elements
                        write_pos -= elems;
                    }
                    i += 1;
                }
                _ => {
                    if write_pos != i {
                        let val = self.stack[i].clone();
                        self.stack[write_pos] = val;
                    }
                    write_pos += 1;
                    i += 1;
                }
            }
        }

        let ghost_size = write_pos - frame_pointer;

        // Move the return value down to write_pos
        for j in 0..ret_size {
            let val = self.stack[ret_start + j].clone();
            self.stack[write_pos + j] = val;
        }
        self.stack.truncate(write_pos + ret_size);

        // Recompute the return value's adopted to include ghost data.
        // The refs in the return value now point into the ghost area,
        // so recompute_adopted naturally picks them up.
        let new_ret_marker = write_pos + ret_size - 1;
        // The return value must be a List (only Lists can contain Refs that
        // trigger compaction). Atomic return values can't reach here.
        if let Val::List { elems, .. } = &self.stack[new_ret_marker] {
            let elems = *elems;
            let new_adopted = recompute_adopted(&self.stack, new_ret_marker, elems);
            self.stack[new_ret_marker] = Val::List { elems, adopted: new_adopted };
        } else {
            debug_assert!(ghost_size == 0, "atomic return value with ghost data");
        }
    }

    pub fn run(mut self) -> Vec<Val> {
        while let Some(&op) = self.ops.get(self.ip) {
            self.run_op(op);
        }
        self.stack
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_push_int() {
        let vm = Vm::new(vec![Op::PushInt(42)]);
        let stack = vm.run();
        assert_eq!(stack.len(), 1);
        assert!(matches!(stack[0], Val::Int(42)));
    }

    #[test]
    fn test_make_list_atomic() {
        let vm = Vm::new(vec![
            Op::PushInt(1),
            Op::PushInt(2),
            Op::MakeList(2),
        ]);
        let stack = vm.run();
        // [1, 2, List{2,0}]
        assert_eq!(stack.len(), 3);
        assert!(matches!(stack[2], Val::List { elems: 2, adopted: 0 }));
    }

    #[test]
    fn test_make_list_nested() {
        // Build [3, 4], then [1, 2, @inner]
        let vm = Vm::new(vec![
            Op::PushInt(3),
            Op::PushInt(4),
            Op::MakeList(2),     // inner = [3, 4] at pos 2
            Op::PushInt(1),
            Op::PushInt(2),
            Op::Copy(2),         // Ref to inner list (offset 2 = skip 1, 2)
            Op::MakeList(3),     // [1, 2, @inner]
        ]);
        let stack = vm.run();
        // Stack: 3, 4, List{2,0}, 1, 2, Ref(2), List{3,3}
        assert_eq!(stack.len(), 7);
        assert!(matches!(stack[2], Val::List { elems: 2, adopted: 0 }));
        assert!(matches!(stack[5], Val::Ref(2)));
        assert!(matches!(stack[6], Val::List { elems: 3, adopted: 3 }));
    }

    #[test]
    fn test_copy_atomic() {
        let vm = Vm::new(vec![
            Op::PushInt(42),
            Op::Copy(0),
        ]);
        let stack = vm.run();
        assert_eq!(stack.len(), 2);
        assert!(matches!(stack[0], Val::Int(42)));
        assert!(matches!(stack[1], Val::Int(42)));
    }

    #[test]
    fn test_copy_creates_ref() {
        let vm = Vm::new(vec![
            Op::PushInt(1),
            Op::PushInt(2),
            Op::MakeList(2),
            Op::Copy(0),
        ]);
        let stack = vm.run();
        assert_eq!(stack.len(), 4);
        assert!(matches!(stack[3], Val::Ref(2)), "got {:?}", stack[3]);
    }

    #[test]
    fn test_get_direct() {
        // [10, 20, 30].get(1) → 20
        let vm = Vm::new(vec![
            Op::PushInt(10),
            Op::PushInt(20),
            Op::PushInt(30),
            Op::MakeList(3),
            Op::Get(1),
        ]);
        let stack = vm.run();
        assert_eq!(stack.len(), 1);
        assert!(matches!(stack[0], Val::Int(20)));
    }

    #[test]
    fn test_get_via_ref() {
        let vm = Vm::new(vec![
            Op::PushInt(10),
            Op::PushInt(20),
            Op::MakeList(2),
            Op::Copy(0),  // Ref to list
            Op::Get(1),   // get element 1 → 20
        ]);
        let stack = vm.run();
        assert!(matches!(stack[stack.len() - 1], Val::Int(20)), "got {:?}", stack);
    }

    #[test]
    fn test_get_nested() {
        // Build [3, 4], then [1, 2, @inner].get(2) → Ref to inner
        let vm = Vm::new(vec![
            Op::PushInt(3),
            Op::PushInt(4),
            Op::MakeList(2),
            Op::PushInt(1),
            Op::PushInt(2),
            Op::Copy(2),
            Op::MakeList(3),
            Op::Get(2),  // gets the Ref to inner list
        ]);
        let stack = vm.run();
        assert!(matches!(stack[stack.len() - 1], Val::Ref(2)), "got {:?}", stack);
    }

    #[test]
    fn test_set_direct() {
        // [10, 20, 30].set(1, 99) → [10, 99, 30]
        let vm = Vm::new(vec![
            Op::PushInt(10),
            Op::PushInt(20),
            Op::PushInt(30),
            Op::MakeList(3),
            Op::PushInt(99),
            Op::Set(1),
        ]);
        let stack = vm.run();
        assert_eq!(stack.len(), 4, "got {:?}", stack);
        assert!(matches!(stack[0], Val::Int(10)));
        assert!(matches!(stack[1], Val::Int(99)));
        assert!(matches!(stack[2], Val::Int(30)));
        assert!(matches!(stack[3], Val::List { elems: 3, adopted: 0 }));
    }

    #[test]
    fn test_set_via_ref() {
        // Set via Ref deep-copies the list (mutable value semantics).
        // The original is untouched.
        let vm = Vm::new(vec![
            Op::PushInt(10),
            Op::PushInt(20),
            Op::MakeList(2),  // original: [10, 20] at positions 0-2
            Op::Copy(0),      // Ref(2)
            Op::PushInt(42),
            Op::Set(0),       // deep-copies, mutates copy
        ]);
        let stack = vm.run();
        // Original is unchanged
        assert!(matches!(stack[0], Val::Int(10)), "original[0]: got {:?}", stack[0]);
        assert!(matches!(stack[1], Val::Int(20)), "original[1]: got {:?}", stack[1]);
        // Copy is on top with element 0 = 42
        let top = stack.len() - 1;
        assert!(matches!(stack[top], Val::List { elems: 2, .. }), "got {:?}", stack[top]);
        let copy_elem0 = top - 2;
        assert!(matches!(stack[copy_elem0], Val::Int(42)), "copy[0]: got {:?}", stack[copy_elem0]);
        let copy_elem1 = top - 1;
        assert!(matches!(stack[copy_elem1], Val::Int(20)), "copy[1]: got {:?}", stack[copy_elem1]);
    }

    #[test]
    fn test_push_list() {
        // Start with [1, 2], push 3 → [1, 2, 3]
        let vm = Vm::new(vec![
            Op::PushInt(1),
            Op::PushInt(2),
            Op::MakeList(2),
            Op::PushInt(3),
            Op::Push,
        ]);
        let stack = vm.run();
        assert!(matches!(stack[stack.len()-1], Val::List { elems: 3, adopted: 0 }), "got {:?}", stack);
        assert!(matches!(stack[0], Val::Int(1)));
        assert!(matches!(stack[1], Val::Int(2)));
        assert!(matches!(stack[2], Val::Int(3)));
    }

    #[test]
    fn test_pop_list() {
        // [1, 2, 3].pop() → [1, 2] and 3
        let vm = Vm::new(vec![
            Op::PushInt(1),
            Op::PushInt(2),
            Op::PushInt(3),
            Op::MakeList(3),
            Op::Pop,
        ]);
        let stack = vm.run();
        assert!(matches!(stack[stack.len()-1], Val::Int(3)), "got {:?}", stack);
        assert!(matches!(stack[2], Val::List { elems: 2, adopted: 0 }), "got {:?}", stack);
    }

    #[test]
    fn test_push_empty_list() {
        let vm = Vm::new(vec![
            Op::MakeList(0),
            Op::PushInt(42),
            Op::Push,
        ]);
        let stack = vm.run();
        assert_eq!(stack.len(), 2, "got {:?}", stack);
        assert!(matches!(stack[0], Val::Int(42)));
        assert!(matches!(stack[1], Val::List { elems: 1, adopted: 0 }));
    }

    #[test]
    fn test_call_return_simple() {
        let vm = Vm::with_ip(vec![
            Op::PushInt(99), // 0: function body
            Op::Return,      // 1
            Op::PushFunc(0), // 2: main entry
            Op::Call(0),     // 3
        ], 2);
        let stack = vm.run();
        assert_eq!(stack.len(), 1);
        assert!(matches!(stack[0], Val::Int(99)));
    }

    #[test]
    fn test_return_no_threatened_refs() {
        let vm = Vm::with_ip(vec![
            Op::PushInt(1),    // 0
            Op::PushInt(2),    // 1
            Op::MakeList(2),   // 2: local list (garbage)
            Op::PushInt(42),   // 3: return this
            Op::Return,        // 4
            Op::PushFunc(0),   // 5
            Op::Call(0),       // 6
        ], 5);
        let stack = vm.run();
        assert_eq!(stack.len(), 1);
        assert!(matches!(stack[0], Val::Int(42)));
    }

    #[test]
    fn test_compaction_example() {
        // Function creates lists A=(1,2), B=(5,6) garbage, C=(3,4).
        // Returns [@A, @C]. B is garbage.
        let vm = Vm::with_ip(vec![
            // Function body:
            Op::PushInt(1),    // 0
            Op::PushInt(2),    // 1
            Op::MakeList(2),   // 2: A = [1,2]
            Op::PushInt(5),    // 3
            Op::PushInt(6),    // 4
            Op::MakeList(2),   // 5: B = [5,6] (garbage)
            Op::PushInt(3),    // 6
            Op::PushInt(4),    // 7
            Op::MakeList(2),   // 8: C = [3,4]
            Op::Copy(6),       // 9: ref to A → Ref(2)
            Op::Copy(1),       // 10: ref to C → Ref(8)
            Op::MakeList(2),   // 11: [@A, @C]
            Op::Return,        // 12
            // Main entry:
            Op::PushFunc(0),   // 13
            Op::Call(0),       // 14
        ], 13);
        let stack = vm.run();

        // After compaction: A kept, B removed, C shifted.
        // Ghost data: A(3 slots) + C(3 slots) = 6 slots
        // Return value: Ref, Ref, List{2, adopted+6}
        // After compaction: A(0-2), C(3-5) kept, B removed.
        // Return: Ref(2), Ref(5), List{2, adopted=6} (span from 0 to elem_start=6)
        assert_eq!(stack.len(), 9, "Expected 9 slots, got {}: {:?}", stack.len(), stack);
        assert!(matches!(stack[0], Val::Int(1)));
        assert!(matches!(stack[1], Val::Int(2)));
        assert!(matches!(stack[2], Val::List { elems: 2, adopted: 0 }));
        assert!(matches!(stack[3], Val::Int(3)));
        assert!(matches!(stack[4], Val::Int(4)));
        assert!(matches!(stack[5], Val::List { elems: 2, adopted: 0 }));
        assert!(matches!(stack[6], Val::Ref(2)));
        assert!(matches!(stack[7], Val::Ref(5)));
        assert!(matches!(stack[8], Val::List { elems: 2, adopted: 6 }));
    }

    #[test]
    fn test_compaction_nested() {
        // Function creates nested list ((1,2), 3) and garbage (9,9).
        // Returns a ref to the nested list.
        let vm = Vm::with_ip(vec![
            // Function body:
            Op::PushInt(1),    // 0
            Op::PushInt(2),    // 1
            Op::MakeList(2),   // 2: inner = [1,2]
            Op::PushInt(3),    // 3
            Op::Copy(1),       // 4: Ref(2) to inner
            Op::MakeList(2),   // 5: outer = [3, @inner] → List{2,3}
            Op::PushInt(9),    // 6
            Op::PushInt(9),    // 7
            Op::MakeList(2),   // 8: garbage = [9,9]
            Op::Copy(3),       // 9: ref to outer → Ref(5)
            Op::MakeList(1),   // 10: wrap in list so compaction runs
            Op::Return,        // 11
            // Main entry:
            Op::PushFunc(0),   // 12
            Op::Call(0),       // 13
        ], 12);
        let stack = vm.run();

        // After compaction: outer (with inner adopted) kept, garbage removed.
        // Ghost data = 6 slots (inner[3] + outer's elements[2] + outer marker[1])
        // Return value = Ref + List marker = 2 slots
        // Stack: [1, 2, List{2,0}, 3, Ref(2), List{2,3}, @5, List{1,7}]
        assert_eq!(stack.len(), 8, "got {:?}", stack);
        assert!(matches!(stack[0], Val::Int(1)));
        assert!(matches!(stack[1], Val::Int(2)));
        assert!(matches!(stack[2], Val::List { elems: 2, adopted: 0 }));
        assert!(matches!(stack[3], Val::Int(3)));
        assert!(matches!(stack[4], Val::Ref(2)));
        assert!(matches!(stack[5], Val::List { elems: 2, adopted: 3 }));
        assert!(matches!(stack[6], Val::Ref(5)));
        assert!(matches!(stack[7], Val::List { elems: 1, adopted: 6 }));
    }

    #[test]
    fn test_if_equal() {
        let vm = Vm::with_ip(vec![
            Op::PushInt(42),                          // 0: if_true
            Op::Return,                               // 1
            Op::PushInt(99),                          // 2: if_false
            Op::Return,                               // 3
            Op::PushInt(1),                           // 4: main
            Op::PushInt(1),                           // 5
            Op::If { if_true: 0, if_false: 2 },      // 6
        ], 4);
        let stack = vm.run();
        assert_eq!(stack.len(), 1);
        assert!(matches!(stack[0], Val::Int(42)));
    }

    #[test]
    fn test_if_not_equal() {
        let vm = Vm::with_ip(vec![
            Op::PushInt(42),
            Op::Return,
            Op::PushInt(99),
            Op::Return,
            Op::PushInt(1),
            Op::PushInt(2),
            Op::If { if_true: 0, if_false: 2 },
        ], 4);
        let stack = vm.run();
        assert_eq!(stack.len(), 1);
        assert!(matches!(stack[0], Val::Int(99)));
    }

    #[test]
    fn test_unpack_direct() {
        // Unpack [10, 20], then collect the unpacked elements into a new list
        // to verify both were placed on the stack.
        let vm = Vm::with_ip(vec![
            Op::MakeList(2), // 0: if_true — collect the 2 unpacked elements
            Op::Return,      // 1
            Op::Return,      // 2: if_false
            Op::PushInt(10),
            Op::PushInt(20),
            Op::MakeList(2),
            Op::Unpack { elems: 2, if_true: 0, if_false: 2 },
        ], 3);
        let stack = vm.run();
        // After unpack+MakeList+Return: [10, 20, List{2,0}]
        assert_eq!(stack.len(), 3, "got {:?}", stack);
        assert!(matches!(stack[0], Val::Int(10)), "got {:?}", stack);
        assert!(matches!(stack[1], Val::Int(20)), "got {:?}", stack);
        assert!(matches!(stack[2], Val::List { elems: 2, adopted: 0 }), "got {:?}", stack);
    }

    #[test]
    fn test_unpack_wrong_count() {
        let vm = Vm::with_ip(vec![
            Op::Return,  // 0: if_true
            Op::Return,  // 1: if_false
            Op::PushInt(10),
            Op::PushInt(20),
            Op::MakeList(2),
            Op::Unpack { elems: 3, if_true: 0, if_false: 1 },
        ], 2);
        let stack = vm.run();
        // Should take if_false, list stays on stack
        assert!(matches!(stack[stack.len() - 1], Val::List { elems: 2, .. }), "got {:?}", stack);
    }

    #[test]
    fn test_size_at() {
        let stack = vec![Val::Int(1)];
        assert_eq!(size_at(&stack, 0), 1);

        let stack = vec![
            Val::Int(1),
            Val::Int(2),
            Val::List { elems: 2, adopted: 0 },
        ];
        assert_eq!(size_at(&stack, 2), 3);

        let stack = vec![
            Val::Int(3),
            Val::Int(4),
            Val::List { elems: 2, adopted: 0 },
            Val::Int(1),
            Val::Int(2),
            Val::Ref(2),
            Val::List { elems: 3, adopted: 3 },
        ];
        assert_eq!(size_at(&stack, 6), 7);
    }

    #[test]
    fn test_call_return_with_args() {
        let vm = Vm::with_ip(vec![
            Op::Copy(0),     // 0: copy the list arg
            Op::Return,      // 1
            Op::PushInt(1),  // 2: main
            Op::PushInt(2),  // 3
            Op::MakeList(2), // 4: [1, 2]
            Op::PushFunc(0), // 5
            Op::Call(3),     // 6: 3 arg slots (2 elems + marker)
        ], 2);
        let stack = vm.run();
        assert!(stack.len() >= 3, "got {:?}", stack);
    }

    #[test]
    fn test_unpack_with_adopted_data() {
        // Unpack a list whose elements include a Ref to adopted data.
        // [1, @inner] where inner = [3, 4].
        // After unpack, the Ref must still point to valid data.
        let vm = Vm::with_ip(vec![
            // if_true: access the second element (the Ref), then Get(0) through it
            Op::Copy(0),     // 0: copy the Ref (second unpacked element, top of stack)
            Op::Get(0),      // 1: dereference → should get 3
            Op::Return,      // 2
            Op::Return,      // 3: if_false
            // main:
            Op::PushInt(3),  // 4
            Op::PushInt(4),  // 5
            Op::MakeList(2), // 6: inner = [3, 4]
            Op::PushInt(1),  // 7
            Op::Copy(1),     // 8: Ref to inner
            Op::MakeList(2), // 9: [1, @inner]
            Op::Unpack { elems: 2, if_true: 0, if_false: 3 }, // 10
        ], 4);
        let stack = vm.run();
        // Should return 3 (first element of inner, accessed via the Ref)
        assert_eq!(stack.len(), 1, "got {:?}", stack);
        assert!(matches!(stack[0], Val::Int(3)), "got {:?}", stack);
    }

    #[test]
    fn test_compaction_with_internal_refs() {
        // Function creates garbage_a, then inner, then garbage_b, then outer
        // which references inner. Returns a ref to outer. After compaction,
        // outer's internal Ref to inner must be correctly updated.
        let vm = Vm::with_ip(vec![
            // Function body:
            Op::PushInt(9),    // 0
            Op::MakeList(1),   // 1: garbage_a = [9]
            Op::PushInt(1),    // 2
            Op::PushInt(2),    // 3
            Op::MakeList(2),   // 4: inner = [1, 2]
            Op::PushInt(3),    // 5
            Op::Copy(1),       // 6: Ref to inner (marker at pos 4, offset=1)
            Op::MakeList(2),   // 7: outer = [3, @inner]
            Op::Copy(0),       // 8: Ref to outer
            Op::MakeList(1),   // 9: wrap to force compaction
            Op::Return,        // 10
            // Main:
            Op::PushFunc(0),   // 11
            Op::Call(0),       // 12
        ], 11);
        let stack = vm.run();
        // After compaction: garbage_a removed, inner shifted down by 2.
        // outer's Ref should point to the shifted inner position.
        // Verify: get element 1 of the return value (the Ref to outer),
        // then get element 1 of outer (the Ref to inner),
        // then get element 0 of inner → should be 1.
        //
        // For now just check the stack is valid and the Ref in outer
        // points to a list containing [1, 2].
        let outer_ref = match &stack[stack.len() - 1] {
            Val::List { .. } => {
                let marker = stack.len() - 1;
                let elems = if let Val::List { elems, .. } = &stack[marker] { *elems } else { 0 };
                let elem_start = marker - elems;
                // First element of the wrapper is a Ref to outer
                stack[elem_start].clone()
            }
            other => panic!("Expected List, got {:?}", other),
        };
        let outer_pos = match outer_ref {
            Val::Ref(pos) => pos,
            other => panic!("Expected Ref to outer, got {:?}", other),
        };
        // outer is a List at outer_pos
        let (outer_elems, _) = match &stack[outer_pos] {
            Val::List { elems, adopted } => (*elems, *adopted),
            other => panic!("Expected outer List, got {:?}", other),
        };
        assert_eq!(outer_elems, 2);
        // Second element of outer should be a Ref to inner
        let inner_ref_pos = outer_pos - outer_elems + 1;
        let inner_pos = match &stack[inner_ref_pos] {
            Val::Ref(pos) => *pos,
            other => panic!("Expected Ref to inner, got {:?}", other),
        };
        // inner should be [1, 2]
        match &stack[inner_pos] {
            Val::List { elems: 2, .. } => {}
            other => panic!("Expected inner List{{2,..}}, got {:?}", other),
        }
        let inner_elem0 = inner_pos - 2; // first element
        assert!(matches!(stack[inner_elem0], Val::Int(1)), "inner[0] should be 1, got {:?}", stack[inner_elem0]);
    }

    /// Regression: a reachable child (A) inside a garbage parent's (B)
    /// adopted zone has its own adopted dependency (Z). Compaction must
    /// transitively mark Z as reachable even though B is garbage.
    #[test]
    fn test_compaction_transitive_mark_through_garbage_parent() {
        let vm = Vm::with_ip(vec![
            // Function body:
            Op::PushInt(99),   // 0
            Op::MakeList(1),   // 1: Z = [99]
            Op::PushInt(2),    // 2
            Op::Copy(1),       // 3: Ref(1) to Z
            Op::MakeList(2),   // 4: A = [2, @Z], adopted covers Z
            Op::PushInt(3),    // 5
            Op::Copy(1),       // 6: Ref(4) to A
            Op::PushInt(4),    // 7
            Op::MakeList(3),   // 8: B = [3, @A, 4], adopted covers A+Z
            Op::Copy(4),       // 9: Ref(4) to A (skip over B's 3 elems + marker)
            Op::MakeList(1),   // 10: return value = [@A]
            Op::Return,        // 11
            // Main:
            Op::PushFunc(0),   // 12
            Op::Call(0),       // 13
        ], 12);
        let stack = vm.run();
        // The return value contains a Ref to A, A contains a Ref to Z,
        // and Z contains 99. Verify the full chain is intact.
        let wrapper = stack.len() - 1;
        let a_ref = match &stack[wrapper] {
            Val::List { elems, .. } => {
                let elem_start = wrapper - elems;
                match &stack[elem_start] {
                    Val::Ref(pos) => *pos,
                    other => panic!("expected Ref to A, got {:?}", other),
                }
            }
            other => panic!("expected List, got {:?}", other),
        };
        let a_elems = match &stack[a_ref] {
            Val::List { elems, .. } => *elems,
            other => panic!("expected A List, got {:?}", other),
        };
        // A's second element (index 1) should be a Ref to Z
        let z_ref_pos = a_ref - a_elems + 1;
        let z_pos = match &stack[z_ref_pos] {
            Val::Ref(pos) => *pos,
            other => panic!("expected Ref to Z, got {:?}", other),
        };
        // Z should be [99]
        match &stack[z_pos] {
            Val::List { elems: 1, .. } => {}
            other => panic!("expected Z List{{1,..}}, got {:?}", other),
        }
        let z_elem = z_pos - 1;
        assert!(matches!(stack[z_elem], Val::Int(99)),
            "Z[0] should be 99, got {:?}", stack[z_elem]);
    }
}
