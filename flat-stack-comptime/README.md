# Flat stack comptime - Comptime output bytecode == runtime input bytecode

By using a bytecode format that's efficient to access and manipulate, the output of comptime evaluation becomes the input of runtime evaluation.

## Motivation

Can we implement a bytecode that is suitable as both the input _and_ the output format of a simple virtual machine, while being represented fully as a sequence of flat operations / values on the stack, without any heap allocation?

Such a unified input/output bytecode with a flat representation of closures makes comptime evaluation much easier, because the result of evaluating a stage is just the same bytecode, without the need to encode/decode references to the heap. This is useful for evaluating macros, for example, or ordinary functions whose arguments are fully available at comptime.

Once we have such a unified input/output bytecode, we can treat the output of one stage as the input of another. That's a good first step if we want to do comptime evaluation, but there's one key piece missing: At runtime we can assume that variables can only appear as part of the _input bytecode_, never as part of the _output_ (because they are resolved during evaluation), but that's not true for comptime evaluation, where we might call a function with unevaluated arguments. Here's an example:

```
y = ... // some value that is not resolved at comptime

f(x) = {
    if (x == y) {
        "equal"
    } else {
        "not equal"
    }
}

// comptime call, with x and y resolving to the same value
f!(y)
```

Without knowing what `y` is bound to, we can see that in the comptime call `!f(y)` both `x` and `y` resolve to the same value, so we could simplify the function call to a concrete if-else expression at comptime and drop the entire function definition of `f` from the runtime bytecode if the function isn't used anywhere else.

But to do that, we need to give our VM the ability to operate on _unresolved_ variables such as `y` at comptime. We cannot guarantee that variables are fully resolved before arguments are passed into a function, which means that the bytecode VM needs to evaluate comptime calls when possible but defer the remaining calls until runtime.

## Outcome

A simple VM in 600 lines of code with a fully unified input/output bytecode representation that stores its values entirely on the main VM stack and supports comptime evaluation of functions whose arguments aren't fully resolved at comptime.

The bytecode is built on the observation that a tree structure with pointers to its child nodes can not only be represented as a flat structure in an array by using array indices instead of pointers, but pointers/indices can even be omitted completely if we represent nodes as operations that manipulate their child nodes as elements on a stack.

This is basically what a bytecode for a stack-based programming languages is: Operands are pushed onto the stack, operations then operate on these values by popping from and pushing to the stack. Since a stack can be represented using a flat, contiguous array, we can achieve much better cache locality by using bytecode instead of a boxed AST that requires a lot of pointer chasing.

The bytecode guarantees several important invariants:

- **One slot per list element / function argument:** Every list element or function argument being accessed occupies exactly 1 slot, which makes indexing elements/arguments `O(1)`.
- **Refs always point backwards:** Every reference points to something that sits lower on the stack, making the entire stack acyclic and enabling linear mark-and-compact passes.
- **Operations track their extent on the stack:** Every operation stores the size of their operands, making it possible to skip past entire part of the operand tree in `O(1)`.
- **Values are self-evaluating, computations aren't:** Values are stable targets for refs across stages, but computations aren't (they might shrink or grow on the output stack), so refs never point to deferred computations.

### Unified bytecode

```
// Ops are atomic ints/variables/references or dynamically sized
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Op {
    Int(i64),
    Var { elem: usize },
    Ref { offset: usize },
    Sized(SizedOp, usize), // the size field allows O(1) access
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SizedOp {
    BlobStart,
    BlobEnd,
    FnStart,
    FnEnd { args: usize },
    Call { args: usize, comptime: bool },
    List { elems: usize },
    Push { elems: usize },
    Set,
    Get,
    If,
    Len,
    Bin(BinOp),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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

### Comptime evaluation

Using a unified input/output representation has the nice property that a _single evaluator_ is enough for both comptime and runtime, since both evaluation stages operate on the same format.

The only difference between the two stages is that at comptime evaluation happens _inside of function bodies_ if they contain comptime calls. The function bodies are evaluated with _symbolic arguments_, in other words unresolved variables instead of concrete values as arguments.

Whenever a comptime function calls a non-comptime function, that function call as well as its transitive function calls are evaluated as they would be under runtime evaluation. This makes it possible to define functions such as `reverse` once and use them transparently during both comptime and runtime, even if they call non-comptime functions.

In other words: Comptime is a property of function _calls_, not function _definitions_, enabling polymorphism across comptime and runtime stages.

Whenever a function at comptime is called with symbolic arguments, the function is evaluated as much as possible. If this isn't possible, for example when one or both of the variables in `x + y` remain unresolved, the call is _deferred_ and re-emitted as bytecode and eventually fully evaluated at runtime.

As a result, comptime calls are evaluated at comptime if possible, but they don't produce errors even if some of their arguments (or even the callee) remain unresolved at comptime. They will instead be re-emitted as comptime calls in the bytecode, giving the consumer of the comptime stage the option of either executing them at runtime or raising an error if comptime calls remain in the bytecode after the comptime stage.

Because comptime calls that cannot be resolved are deferred, the termination behavior for comptime is the same as for runtime: Comptime calls only diverge if they would diverge at runtime anyway, because recursion that depends on a runtime value is cut off at comptime (since its inputs are unresolved).

Going back to the initial example of comptime evaluating `f`, here's how the bytecode would change from comptime to runtime:

```
 0  FnStart(10)        f = (x, y') => if (x == y') 1 else 0
 1    FnStart(1)         \  then-arm
 2      Int(1)           |
 3    FnEnd{0}(1)        /
 4    FnStart(1)         \  else-arm
 5      Int(0)           |
 6    FnEnd{0}(1)        /
 7    Var{0}                x
 8    Var{1}                y'
 9    Bin(Eq)
10    If
11  FnEnd{2}(10)
12  FnStart(4)         outer = (y) => f!(y, y)
13    Ref -----> 11       -> f
14    Var{0}
15    Var{0}
16    Call{2, comptime}
17  FnEnd{1}(4)
```

The output of the comptime stage is the following simplified program:

```
 0  FnStart(1)         \  then-arm, extracted from f
 1    Int(1)           |
 2  FnEnd{0}(1)        /
 3  FnStart(1)         \  else-arm
 4    Int(0)           |
 5  FnEnd{0}(1)        /
 6  FnStart(6)         outer = (y) => if (y == y) 1 else 0
 7    Ref ----->  2       -> then-arm
 8    Ref ----->  5       -> else-arm
 9    Var{0}              y   \  both of f's params became the same var
10    Var{0}              y   /  of outer, substitution by copy
11    Bin(Eq)(2)
12    If(5)               deferred, extent covers its three operands
13  FnEnd{1}(6)
```

### 2-pass mark-and-compact

Two linear passes run on function return, amortized:

- Pass 1, mark top to bottom: Run through the “threatened area” (everything allocated on the stack as part of the function) and transitively mark all refs reachable from the return value. Since refs only point down the stack, this is a linear pass.
- Pass 2, compact bottom to top: Now that we know what's garbage, run through the stack and keep track of how much garbage has been compacted. Increase this counter when we encounter garbage, and move everything that's not garbage by this amount down the stack, _but store by how much the value has been shifted at the old location_ so that old refs still resolve and can be “redirected” by that amount.

Note how we need to keep track of how far data has been shifted _after_ we have shifted it, because we will encounter refs to it later on the stack as we move closer to the top. This means that moving data down the stack _must not overwrite_ this meta information. The solution is to split each stack slot into a fixed part for the `Op` and a separate fixed part for the meta information, holding the tag that identifies an operation as well as a mark bit (for reachability during the first pass) and the amount by which an operation has been shifted during compaction.

All of this makes garbage collection trivial. It runs on return (whenever the size of the threatened area minus return value exceeds the size of the return value, leading to amortized compaction for incremental garbage) and the entire function is short enough to fit in less than 60 lines of code.
