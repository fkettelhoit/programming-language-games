use criterion::{Criterion, criterion_group, criterion_main, BenchmarkId};
use flat_stack_lists::Op;

// ============================================================================
// Benchmark suite: flat stack VM vs cons-list VM
//
// Operations: build, iter_left, iter_right, drain, reverse, map, return_escape
// Sizes: 10, 1000
// ============================================================================

// ---------------------------------------------------------------------------
// Helpers: In the flat VM, a list of n atomic elements occupies n+1 stack
// slots (n elements + 1 marker). Copy(offset) counts slots from the top.
// In the cons VM, a list occupies 1 slot. So Copy offsets differ.
// Functions returning (flat_ops, cons_ops) handle this.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// BUILD: Start empty, Push n elements one at a time
// Same bytecode for both VMs (Push always works on the top value).
// ---------------------------------------------------------------------------

fn build(n: usize) -> Vec<Op> {
    let mut ops = vec![Op::MakeList(0)];
    for i in 0..n {
        ops.push(Op::PushInt(i as i64));
        ops.push(Op::Push);
    }
    ops
}

// ---------------------------------------------------------------------------
// ITER_LEFT: Create list, Get(0), Get(1), ..., Get(n-1)
// Each Get via Copy+Get. After each, 1 scalar accumulates on the stack.
//
// Flat: list occupies n+1 slots. After k Gets, k scalars above it.
//   Copy offset = k (skip k scalars) to reach the list marker.
// Cons: list occupies 1 slot. After k Gets, k scalars above it.
//   Copy offset = k.
// Same bytecode!
// ---------------------------------------------------------------------------

fn iter_left(n: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    for i in 0..n { ops.push(Op::PushInt(i as i64)); }
    ops.push(Op::MakeList(n));
    for k in 0..n {
        ops.push(Op::Copy(k)); // skip k accumulated scalars
        ops.push(Op::Get(k));
    }
    ops
}

// ---------------------------------------------------------------------------
// ITER_RIGHT: Same but Get(n-1), ..., Get(0)
// ---------------------------------------------------------------------------

fn iter_right(n: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    for i in 0..n { ops.push(Op::PushInt(i as i64)); }
    ops.push(Op::MakeList(n));
    for k in 0..n {
        ops.push(Op::Copy(k));
        ops.push(Op::Get(n - 1 - k));
    }
    ops
}

// ---------------------------------------------------------------------------
// DRAIN: Create list, Pop n times (discarding the popped element each time
// by wrapping in a 2-element list and getting element 0).
// ---------------------------------------------------------------------------

fn drain_pop_discard(ops: &mut Vec<Op>, n: usize) {
    for k in 0..n {
        ops.push(Op::Pop);
        if k < n - 1 {
            ops.push(Op::MakeList(2));
            ops.push(Op::Get(0));
        }
    }
}

fn drain(n: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    for i in 0..n { ops.push(Op::PushInt(i as i64)); }
    ops.push(Op::MakeList(n));
    drain_pop_discard(&mut ops, n);
    ops
}

// ---------------------------------------------------------------------------
// REVERSE: Extract all elements in reverse order, build new list.
// Phase 1: Copy+Get for k = n-1, n-2, ..., 0 (produces n scalars)
// Phase 2: MakeList(n)
// ---------------------------------------------------------------------------

fn reverse(n: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    for i in 0..n { ops.push(Op::PushInt(i as i64)); }
    ops.push(Op::MakeList(n));
    for k in 0..n {
        ops.push(Op::Copy(k));
        ops.push(Op::Get(n - 1 - k));
    }
    ops.push(Op::MakeList(n));
    ops
}

// ---------------------------------------------------------------------------
// MAP: Read each element, create (elem, elem) pair, collect into new list.
//
// For each k: Copy(offset_to_source), Get(k), Copy(0), MakeList(2)
// Then MakeList(n).
//
// Flat: each pair = 3 slots on stack (2 ints + marker). Source list is below.
//   After k pairs: offset to source marker = 3*k.
// Cons: each pair = 1 slot. offset = k.
// ---------------------------------------------------------------------------

fn map_flat(n: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    for i in 0..n { ops.push(Op::PushInt(i as i64)); }
    ops.push(Op::MakeList(n));
    for k in 0..n {
        let offset = 3 * k; // each pair is 3 flat slots
        ops.push(Op::Copy(offset));
        ops.push(Op::Get(k));
        ops.push(Op::Copy(0));
        ops.push(Op::MakeList(2));
    }
    ops.push(Op::MakeList(n));
    ops
}

fn map_cons(n: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    for i in 0..n { ops.push(Op::PushInt(i as i64)); }
    ops.push(Op::MakeList(n));
    for k in 0..n {
        let offset = k; // each pair is 1 slot
        ops.push(Op::Copy(offset));
        ops.push(Op::Get(k));
        ops.push(Op::Copy(0));
        ops.push(Op::MakeList(2));
    }
    ops.push(Op::MakeList(n));
    ops
}

// ---------------------------------------------------------------------------
// RETURN_ESCAPE: Function creates n lists, returns refs to half of them.
// The other half is garbage that must be compacted (flat) or just ignored (cons).
//
// Flat: exercises the 4-pass mark-and-compact.
// Cons: trivial return (everything is heap-allocated).
//
// Flat bytecode: must use Copy with offsets counting multi-slot lists.
// Cons bytecode: uses Copy with 1-slot offsets.
// ---------------------------------------------------------------------------

fn return_escape_flat(n: usize) -> Vec<Op> {
    let keep_count = (n + 1) / 2;
    let mut ops = Vec::new();

    // Function body at offset 0: create n single-element lists
    for i in 0..n {
        ops.push(Op::PushInt(i as i64));
        ops.push(Op::MakeList(1)); // each list: 2 slots (elem + marker)
    }
    // Stack: 2n slots. List k's marker is at position 2*k+1.
    // Copy refs to even-indexed lists.
    let mut ref_count = 0;
    for k in 0..n {
        if k % 2 == 0 {
            let offset = 2 * n + ref_count - 2 - 2 * k;
            ops.push(Op::Copy(offset));
            ref_count += 1;
        }
    }
    ops.push(Op::MakeList(keep_count));
    ops.push(Op::Return);

    let main_ip = ops.len();
    ops.push(Op::PushFunc(0));
    ops.push(Op::Call(0));
    ops.push(Op::PushInt(main_ip as i64)); // sentinel for main_ip
    ops
}

fn return_escape_cons(n: usize) -> Vec<Op> {
    let keep_count = (n + 1) / 2;
    let mut ops = Vec::new();

    // Function body at offset 0
    for i in 0..n {
        ops.push(Op::PushInt(i as i64));
        ops.push(Op::MakeList(1));
    }
    // In cons VM, each MakeList(1) produces 1 slot.
    // Stack: n slots. List k is at position k.
    let mut ref_count = 0;
    for k in 0..n {
        if k % 2 == 0 {
            // Offset from top: (n + ref_count - 1) - k
            let offset = n + ref_count - 1 - k;
            ops.push(Op::Copy(offset));
            ref_count += 1;
        }
    }
    ops.push(Op::MakeList(keep_count));
    ops.push(Op::Return);

    let main_ip = ops.len();
    ops.push(Op::PushFunc(0));
    ops.push(Op::Call(0));

    ops.push(Op::PushInt(main_ip as i64)); // sentinel
    ops
}

// ---------------------------------------------------------------------------
// MUTATE: Create a list of n elements, then Set every element to a new value.
//
// Flat: Set on a direct list replaces the element in place. O(1) per Set.
// Cons: Set copies the spine to the target position. O(n-k) per Set(k)
// due to reversed storage (physical position n-1-k).
//
// Same bytecode for both VMs.
// ---------------------------------------------------------------------------

fn mutate(n: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    for i in 0..n { ops.push(Op::PushInt(i as i64)); }
    ops.push(Op::MakeList(n));
    for k in 0..n {
        ops.push(Op::PushInt(1000 + k as i64));
        ops.push(Op::Set(k));
    }
    ops
}

// ---------------------------------------------------------------------------
// BUILD_NESTED: Build a list of n pairs, where each pair is [2k, 2k+1].
//
// Flat: create all n pairs on the stack (3 slots each), then Copy each
// pair's marker to produce a Ref, then MakeList(n) collects the Refs.
// The pairs become adopted data.
//
// Cons: create all n pairs, then MakeList(n). Each pair is 1 slot.
// ---------------------------------------------------------------------------

fn build_nested_flat(n: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    // Create n pairs (each 3 slots: 2 ints + marker)
    for k in 0..n {
        ops.push(Op::PushInt(2 * k as i64));
        ops.push(Op::PushInt(2 * k as i64 + 1));
        ops.push(Op::MakeList(2));
    }
    // Stack: 3n slots. Pair k's marker is at position 3k+2.
    // Copy a Ref to each pair's marker.
    for k in 0..n {
        // After k refs pushed, stack len = 3n + k.
        // Pair k's marker at position 3k + 2.
        // Offset = (3n + k - 1) - (3k + 2) = 3n - 2k - 3.
        let offset = 3 * n - 2 * k - 3;
        ops.push(Op::Copy(offset));
    }
    ops.push(Op::MakeList(n));
    ops
}

fn build_nested_cons(n: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    for k in 0..n {
        ops.push(Op::PushInt(2 * k as i64));
        ops.push(Op::PushInt(2 * k as i64 + 1));
        ops.push(Op::MakeList(2));
    }
    ops.push(Op::MakeList(n));
    ops
}

// ---------------------------------------------------------------------------
// ITER_NESTED: Build a list of n pairs, then for each element get it and
// read its first field. Tests access into nested compound data.
//
// After building, Copy(0) produces a Ref (flat) or Rc clone (cons) for
// non-destructive iteration. Then for each k:
//   Copy(k), Get(k), Get(0)
// Get(k) returns a Ref to the pair (flat) or a cons pair (cons).
// Get(0) on that returns the first field (an Int).
//
// Flat: O(1) per pair access. Cons: O(n) per Get(k) due to chain walk.
// ---------------------------------------------------------------------------

fn iter_nested_flat(n: usize) -> Vec<Op> {
    let mut ops = build_nested_flat(n);
    ops.push(Op::Copy(0)); // Ref to outer list
    for k in 0..n {
        ops.push(Op::Copy(k)); // skip k accumulated Ints
        ops.push(Op::Get(k));
        ops.push(Op::Get(0));
    }
    ops
}

fn iter_nested_cons(n: usize) -> Vec<Op> {
    let mut ops = build_nested_cons(n);
    ops.push(Op::Copy(0)); // clone Rc
    for k in 0..n {
        ops.push(Op::Copy(k));
        ops.push(Op::Get(k));
        ops.push(Op::Get(0));
    }
    ops
}

// ---------------------------------------------------------------------------
// FORK: Create a list, make an independent copy, modify one element in the
// copy. Tests the cost of creating a divergent version of a list.
//
// Cons: Copy clones the Rc (O(1)). Set(n/2) copies the spine to the
// modification point, sharing the rest. Total: O(n/2).
//
// Flat: no way to create an independent copy via Ref (all Refs share the
// same physical data). Must deep-copy by extracting all elements and
// rebuilding. Total: O(n) copy + O(1) Set = O(n).
//
// This is a case where cons's structural sharing wins.
// ---------------------------------------------------------------------------

fn fork_flat(n: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    for i in 0..n { ops.push(Op::PushInt(i as i64)); }
    ops.push(Op::MakeList(n));
    // Deep copy: get a Ref, extract every element, rebuild.
    ops.push(Op::Copy(0)); // Ref to original
    for k in 0..n {
        ops.push(Op::Copy(k)); // skip k accumulated Ints
        ops.push(Op::Get(k));
    }
    ops.push(Op::MakeList(n)); // independent copy
    // Modify middle element of the copy
    ops.push(Op::PushInt(999));
    ops.push(Op::Set(n / 2));
    ops
}

fn fork_cons(n: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    for i in 0..n { ops.push(Op::PushInt(i as i64)); }
    ops.push(Op::MakeList(n));
    // Shallow copy (Rc clone). The spine is copied lazily by Set.
    ops.push(Op::Copy(0));
    // Modify middle element of the copy
    ops.push(Op::PushInt(999));
    ops.push(Op::Set(n / 2));
    ops
}

// ---------------------------------------------------------------------------
// MULTI_FORK: Create a base list of n elements, then fork it n times. Each
// fork creates an independent copy with the last element modified.
//
// This is where cons's structural sharing pays off. Per fork:
//   Cons: Copy (O(1) Rc clone) + Set(n-1) (physical position 0, O(1)) = O(1)
//   Flat: Set via Ref deep-copies the entire list (O(n)) = O(n)
// Total: cons O(n) vs flat O(n^2).
//
// The flat VM's Copy offset grows with each fork because each deep-copied
// list adds n+1 slots to the stack. The cons VM's offset grows by 1 per fork.
// ---------------------------------------------------------------------------

fn multi_fork_flat(n: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    for i in 0..n { ops.push(Op::PushInt(i as i64)); }
    ops.push(Op::MakeList(n));
    // Each fork: Copy(offset to base) + Set(n-1) via Ref (triggers deep copy).
    // After j forks, each fork is n+1 slots. Base marker is at position n.
    // Offset to base = j * (n + 1).
    for j in 0..n {
        let offset = j * (n + 1);
        ops.push(Op::Copy(offset));
        ops.push(Op::PushInt(1000 + j as i64));
        ops.push(Op::Set(n - 1));
    }
    ops
}

fn multi_fork_cons(n: usize) -> Vec<Op> {
    let mut ops = Vec::new();
    for i in 0..n { ops.push(Op::PushInt(i as i64)); }
    ops.push(Op::MakeList(n));
    // Each fork: Copy(offset to base) + Set(n-1).
    // After j forks, each fork is 1 slot. Base is at position 0. Offset = j.
    for j in 0..n {
        ops.push(Op::Copy(j));
        ops.push(Op::PushInt(1000 + j as i64));
        ops.push(Op::Set(n - 1));
    }
    ops
}

// ============================================================================
// Benchmark runners
// ============================================================================

fn run_bench_same(c: &mut Criterion, name: &str, make_ops: fn(usize) -> Vec<Op>) {
    let mut group = c.benchmark_group(name);
    for n in [10, 1000] {
        let ops = make_ops(n);
        group.bench_with_input(BenchmarkId::new("flat", n), &n, |b, _| {
            b.iter(|| {
                let vm = flat_stack_lists::Vm::new(ops.clone());
                vm.run()
            });
        });
        group.bench_with_input(BenchmarkId::new("cons", n), &n, |b, _| {
            b.iter(|| {
                let vm = flat_stack_lists::traditional::Vm::new(ops.clone());
                vm.run()
            });
        });
    }
    group.finish();
}

fn run_bench_split(
    c: &mut Criterion,
    name: &str,
    gen_flat: fn(usize) -> Vec<Op>,
    gen_cons: fn(usize) -> Vec<Op>,
) {
    let mut group = c.benchmark_group(name);
    for n in [10, 1000] {
        let flat_ops = gen_flat(n);
        let cons_ops = gen_cons(n);
        group.bench_with_input(BenchmarkId::new("flat", n), &n, |b, _| {
            b.iter(|| {
                let vm = flat_stack_lists::Vm::new(flat_ops.clone());
                vm.run()
            });
        });
        group.bench_with_input(BenchmarkId::new("cons", n), &n, |b, _| {
            b.iter(|| {
                let vm = flat_stack_lists::traditional::Vm::new(cons_ops.clone());
                vm.run()
            });
        });
    }
    group.finish();
}

fn run_bench_escape(c: &mut Criterion) {
    let mut group = c.benchmark_group("return_escape");
    for n in [10, 1000] {
        // Build flat ops
        let flat_all = return_escape_flat(n);
        let flat_main_ip = flat_all[flat_all.len() - 1].clone();
        let flat_main_ip = if let Op::PushInt(ip) = flat_main_ip { ip as usize } else { panic!() };
        let flat_ops: Vec<Op> = flat_all[..flat_all.len() - 1].to_vec();

        // Build cons ops
        let cons_all = return_escape_cons(n);
        let cons_main_ip = cons_all[cons_all.len() - 1].clone();
        let cons_main_ip = if let Op::PushInt(ip) = cons_main_ip { ip as usize } else { panic!() };
        let cons_ops: Vec<Op> = cons_all[..cons_all.len() - 1].to_vec();

        group.bench_with_input(BenchmarkId::new("flat", n), &n, |b, _| {
            b.iter(|| {
                let vm = flat_stack_lists::Vm::with_ip(flat_ops.clone(), flat_main_ip);
                vm.run()
            });
        });
        group.bench_with_input(BenchmarkId::new("cons", n), &n, |b, _| {
            b.iter(|| {
                let vm = flat_stack_lists::traditional::Vm::with_ip(cons_ops.clone(), cons_main_ip);
                vm.run()
            });
        });
    }
    group.finish();
}

fn bench_all(c: &mut Criterion) {
    run_bench_same(c, "build", build);
    run_bench_same(c, "iter_left", iter_left);
    run_bench_same(c, "iter_right", iter_right);
    run_bench_same(c, "drain", drain);
    run_bench_same(c, "reverse", reverse);
    run_bench_split(c, "map", map_flat, map_cons);
    run_bench_escape(c);
    run_bench_same(c, "mutate", mutate);
    run_bench_split(c, "build_nested", build_nested_flat, build_nested_cons);
    run_bench_split(c, "iter_nested", iter_nested_flat, iter_nested_cons);
    run_bench_split(c, "fork", fork_flat, fork_cons);
    run_bench_split(c, "multi_fork", multi_fork_flat, multi_fork_cons);
}

criterion_group!(benches, bench_all);
criterion_main!(benches);
