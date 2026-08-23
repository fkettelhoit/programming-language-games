# Flat stack closures - Closures entirely on the stack

Instead of moving values onto the heap when they would outlive the stack as part of a closure, what if closures lived entirely on the stack, mark-and-compacted, with good locality?

## Motivation

Keeping values on the stack is simple until a value needs to outlive a function's call frame, for example as part of a closure that is being returned. One option is to move all of the values that need to be kept alive to the heap. However, this has a few disadvantages:

- Instead of living on the stack, the closed-over value lives far away on the stack. If the closure is called with other arguments, these direct arguments will be on the stack, while the closed-over values live on the heap,potentially leading to bad data locality.
- If the goal is to allow staged evaluation / comptime evaluation, the result of a comptime evaluation can now be a closure which relies on heap allocated data, instead of being a flat sequence of bytecode on the stack.

The second disadantage is the main motivation here: Can we implement a bytecode that is suitable as both the input _and_ the output format of a simple virtual machine, while being represented fully as a sequence of flat operations / values on the stack, without any heap allocation?

Such a unified input-output bytecode with a flat representation of closures makes comptime evaluation much easier, because the result of evaluating a stage is just the same bytecode, without the need to encode/decode references to the heap.

## Outcome

A simple VM in 500 lines of code with a fully unified input/output bytecode representation that stores closures entirely on the main VM stack. Any values that would outlive a function return are mark-and-compacted using a simple 2-pass algorithm.

The bytecode guarantees several important invariants:

- **One slot per list element / function argument:** Every list element or function argument being accessed occupies exactly 1 slot, which makes indexing elements/arguments `O(1)`.
- **Refs always point backwards:** Every reference points to something that sits lower on the stack, making the entire stack acyclic and enabling linear mark-and-compact passes.
- **Operations track their extent on the stack:** Every operation stores the size of their operands, making it possible to skip past entire part of the operand tree in `O(1)`.

### Unified bytecode

```
// Ops are atomic ints/variables/references or dynamically sized
pub enum Op {
    Int(i64),
    Var { elem: usize },
    Ref { offset: usize },
    Sized(SizedOp, usize), // the size field allows O(1) access
}

pub enum SizedOp {
    BlobStart,
    BlobEnd,
    FuncStart,
    FuncEnd { args: usize },
    Call { args: usize },
    List { elems: usize },
    Push { elems: usize },
    Set,
    Get,
    If,
    Len,
    Bin(BinOp),
}

pub enum BinOp {
    Eq,
    Add,
    Sub,
    Mul,
}
```

The crucial detail is that all operations track their _size_ on the stack, which makes the representation suitable as a fast `O(1)` output value representation on the stack in addition to being an input bytecode representation. It's possible to read the stack _starting at the top_ and know immediately how many stack slots the topmost element takes up.

By tracking the size of operations + operands, the bytecode representation becomes an AST/bytecode hybrid, making it possible to manipulate and rewrite parts of the AST without being a dumb input-only tape. Since the output stack that is being manipulated uses the same representation as the input stack (in fact, the program being executed is simply a fixed prefix of the “output” stack), the result of running the VM is another stack of bytecode, which can be executed again, opening the door for staged evaluation.

While the representation is the same for input and output, some of the operations undergo a transformation as they are being executed: For example, the operation `Ref { offset: usize }` is used to reference/borrow an element earlier on the stack, with its `offset` referring to a position in the _input bytecode_ (relative to the current instruction pointer) when the operation is executed, but is stored on the output stack with its `offset` referring to a position on the _output stack_ (relative to its own position on the output stack). Depending on whether it is an input instruction or output data, the offset thus takes on a different meaning.

The same is true for `Call { args: usize }` and `List { elems: usize }` instructions, which both store a _logical number of operands_ (each of which can take up multiple stack slots) in addition to the `usize` field of stack slots that each `Op::Sized` tracks. When used as input instructions, there's no requirement that the `args`/`elems` are atomic. But for lists or call frames on the stack, the requirement is that each argument or element is atomic (which means complex values need to be stored lower on the stack and then referenced) so that knowing the logical number of elements allows accessing the atomic elements in `O(1)`.

Here's the stack layout of `[[1, 2], 3, 4]` as input bytecode:

```
Int(1)            \  \
Int(2)            |  |
List { elems: 2 } /  |
Int(3)               |
Int(4)               |
List { elems: 3 }    /
```

Executing it turns the first argument into an atomic reference and copies the other two:

```
Int(1)            \
Int(2)            |
List { elems: 2 } / <--+
Int(3)                 |   // garbage
Int(4)                 |   // garbage
Ref { offset: 3 } -----+ \
Int(3)                   |
Int(4)                   |
List { elems: 3 }        /
```

Note how `Int(3)` and `Int(4)` just get copied and thus leave garbage on the stack, which will be reclaimed by the mark-and-compact algorithm that runs on return.

### 2-pass mark-and-compact

Two linear passes run on function return, amortized:

- Pass 1, mark top to bottom: Run through the “threatened area” (everything allocated on the stack as part of the function) and transitively mark all refs reachable from the return value. Since refs only point down the stack, this is a linear pass.
- Pass 2, compact bottom to top: Now that we know what's garbage, run through the stack and keep track of how much garbage has been compacted. Increase this counter when we encounter garbage, and move everything that's not garbage by this amount down the stack, _but store by how much the value has been shifted at the old location_ so that old refs still resolve and can be “redirected” by that amount.

Note how we need to keep track of how far data has been shifted _after_ we have shifted it, because we will encounter refs to it later on the stack as we move closer to the top. This means that moving data down the stack _must not overwrite_ this meta information. The solution is to split each stack slot into a fixed part for the `Op` and a separate fixed part for the meta information, holding the tag that identifies an operation as well as a mark bit (for reachability during the first pass) and the amount by which an operation has been shifted during compaction.

All of this makes garbage collection trivial. It runs on return (whenever the size of the threatened area minus return value exceeds the size of the return value, leading to amortized compaction for incremental garbage) and the entire function is short enough to fit in less than 50 lines of code.

### Closures

Given the above bytecode + mark-and-compact on return there's barely anything else needed in the VM, because closures end up being just a combination of lists and functions. The calling convention for functions on the stack is function first, then arguments from left to right, so that `f(a, b, c)` on the stack would be represented as `f, a, b, c, Call { args: 3 }`, with `f` and its arguments standing in for one or more stack slots.

The compiler is expected to do closure conversion, so that a function that is identical to `f` but with the first argument coming from an outer scope is first converted into a three argument `f(a, b, c)`. At the point where the closure `f(a, _, _)` is returned, we then simply store `f` and `a` together _in a list_, with `f` as the first element and `a` as the second.

When the closure is applied to its remaining two arguments `b` and `c`, we encounter a stack of the following form, with `f` and its arguments again standing in for one or more stack slots:

```
f, a, List { elems: 2 }, b, c, Call { args: 2 }
```

This is _almost_ like the non-closure call `f, a, b, c, Call { args: 3 }`, except for the `List { elems: 2 }` and the different `args` count. So all we need to turn the closure into a regular call is to move around the arguments on the stack before treating it like a call with 3 arguments. And here's where the requirement that _both_ `Call` and `List` store arguments as _atomic_ elements comes in, because we can always trivially and cheaply move around atomic elements without moving the underlying data of references.

The result is a regular function call. And since the captured arguments of a closure are just stored in a list, the mark-and-compact that happens on return ensures that garbage is compacted by the time the closure leaves its frame. The closure remains stored on the stack, as a flat list.
