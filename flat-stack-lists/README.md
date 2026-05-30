# Flat stack lists -- Compound data on the stack with mark-and-compact on return

What would a functional programming language with immutable values look like if we kept all values (even structs and arrays) entirely on the stack, without needing a static type system?

## Motivation

Functional languages typically represent compound data as heap-allocated, pointer-linked structures (cons cells, boxed tuples). This is flexible but scatters data across the heap, causing pointer chasing and cache misses. C-style structs are contiguous and cache-friendly but require static types to know their layout.

The idea is to keep compound data flat on the stack in a dynamically typed setting. A list is not a chain of heap-allocated cons cells but a contiguous sequence of stack slots with a marker that tracks its extent. Copying a list produces a lightweight reference (a stack position). Mutation through a single-owner reference can happen in place.

The tricky part: when a function returns, its stack frame is about to be reclaimed. If the return value contains references to data in the dying frame, that data must survive. Rather than moving it to the heap, we compact the referenced data in place and attach it to the return value as invisible "ghost data."

## Outcome

The experiment implements two bytecode VMs that execute the same instruction set:

- A **flat VM** that keeps lists on the stack as `[adopted_data..., elem_0, ..., elem_n, List{n, adopted}]`, where each element is exactly one stack slot (either an atomic value or a Ref to another list). On function return, a 4-pass mark-and-compact algorithm preserves referenced data as ghost data attached to the return value.

- A **cons-list VM** (for comparison) where lists are heap-allocated cons chains with reference counting, as in a traditional Lisp.

Benchmarks at n=1000 elements (flat vs cons-list VM):

- **build** (push 1000 elements one at a time): flat 10us, cons 54us. Both O(1) per push. Flat wins ~5x (no heap allocation).
- **iterate** (get every element by index): flat 10-19us, cons 2.1-3.9ms. Flat O(1) per access vs cons O(n). ~200x.
- **reverse** (read all in reverse, build new list): flat 13us, cons 2.5ms. ~190x.
- **map** (read each element, wrap in pair, collect): flat 20us, cons 2.2ms. ~110x.
- **drain** (pop all elements): flat 16us, cons 91us. Both O(1) per pop. Flat wins ~6x (no RC overhead).
- **return with compaction** (create n lists in a function, return refs to half): flat 17us, cons 58us. Flat ~3x faster despite running the 4-pass mark-and-compact.
- **mutate** (set every element of a direct 1000-element list): flat 10us, cons 18ms. Flat O(1) per Set vs cons O(n) spine-copying. ~1800x. Note: cons lists are the wrong data structure for random-access mutation. A real language would use a tree or vector. The flat VM's advantage is that one data structure handles both sequential and random-access patterns.
- **build nested** (build a list of 1000 pairs): flat 21us, cons 92us. ~4x.
- **iterate nested** (build list of 1000 pairs, then read first field of each): flat 32us, cons 2.0ms. ~63x.
- **fork** (deep-copy a 1000-element list, modify one element of the copy): flat 13us, cons 55us. ~4x. A single fork doesn't show cons's sharing advantage because the absolute cost of one deep copy (stack operations) is less than one spine copy (heap allocations).
- **multi_fork** (fork a 1000-element list 1000 times, modifying the last element each time): flat 4.9ms, cons 1.4ms. Cons wins ~3.4x. This is the persistent data structure pattern: each fork on cons is O(1) (Rc clone + O(1) Set at the physical head), while flat pays O(n) per fork (deep copy via Set-via-Ref). Total: cons O(n) vs flat O(n^2).

## Approach

### Stack layout

A list of n elements occupies `n + adopted + 1` stack slots:

```
3          \
4           > adopted data (inner list, 3 slots)
List{2,0}  /
1          \
2           > elements (3 slots, each exactly 1 slot)
Ref ---------> points to the inner list marker above
List{3,3}  <- marker: 3 elements, 3 adopted slots
```

The `adopted` field tracks how many slots below the element area belong to this list's referenced child data. Every element is exactly one stack slot: either an atomic value (Int, Str, Func) or a Ref pointing to another list's marker. This guarantees O(1) random access by index.

### Operations

- **Copy** produces a Ref (a stack position) rather than duplicating data.
- **Get(k)** on a direct list is destructive (consumes the list, returns the element). Get via Ref is non-destructive.
- **Set(k)** on a direct list mutates the element in place (O(1)). Set via Ref deep-copies the list first (mutable value semantics), so other Refs to the same list are unaffected.
- **Push/Pop** append to or remove from the end of the element area.

### Mark-and-compact on return

When a function returns a value containing Refs into its own (dying) stack frame, the referenced data is compacted in place using four linear passes over the threatened area:

1. **Mark** (top to bottom): Set a mark bit on each List marker reachable from the return value's Refs. Propagate marks transitively to structurally nested children via an `inside_floor` variable.
2. **Compute gaps** (bottom to top): Walk marked/unmarked markers, accumulating a running gap from garbage. Store the gap in each reachable marker's `adopted` field (used as scratch space).
3. **Fix Refs** (full scan): Adjust every Ref's target by its target marker's gap.
4. **Compact** (bottom to top): Slide reachable data down, roll back write position past garbage. Recompute each marker's `adopted` from the compacted layout.

The compacted data becomes ghost data attached to the return value by inflating its `adopted` field. From the caller's perspective, the return value is just a list with a larger extent.

## Notes

- [Flat tuples and arrays without pointer soup](https://fredkettelhoit.com/notes/2026/02/28.html)
- [Ghost data: compacting escaped values on the stack](https://fredkettelhoit.com/notes/2026/03/07.html)
- [Flat and immutable lists (on the stack)](https://fredkettelhoit.com/notes/2026/03/15.html)
