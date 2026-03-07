# Reasonable macros — Pattern matching as a library

Can a language allow everything to be redefined (even variable assignment and pattern matching) while keeping the scope of variables immediately obvious? Without evaluating any macros?

## Motivation

Programming languages face a tension between the ability to extend them dynamically and the ability to reason about them statically. Constructs that _bind variables_, such as function definitions or pattern matching, are usually a fixed part of a language's core syntax, unless we go for Lisp-like macros, which are powerful but hard to reason about.

The problem with macros is that just seeing an expression such as `f(2 + 2)` in the source code does not guarantee that it is equivalent to `f(4)`, because `f` could be a macro and thus treat `2 + 2` differently from `4`. By exposing all of the syntactic structure of a program, macros have to be used sparingly and/or expanded before it is possible to reason about equivalent expressions.

There is an unexplored middle ground, however, of allowing binding constructs to be defined and extended, while ensuring that all variables are lexically bound and that their scope can be determined statically.

## Outcome

This experiment implements a minimal language where pattern matching with unification is defined entirely as a library (without any built-in support for matching), while respecting a single guiding principle:

_Every construct in the language can be redefined, there are no privileged language constructs. But the scope of variables remains immediately obvious, just by looking at the source code, without evaluating any function or macro._

## Approach

The key question is: how does a reader know whether a name is being _bound_ or _used_? Most languages do not visually distinguish these two cases:

```
a + b // the variable a is being used
a = b // the variable a is being bound
```

In the first case, `a` is looked up in the current scope, whereas in the second case, `a` is a fresh variable that will be bound. That they play such different roles is not visible just by looking at the variables, nor by looking at the operators, because `+` and `=` are both infix symbols.

### Explicit bindings (the [`explicit/`](explicit/) variant)

One approach is to make bindings syntactically explicit. The `$` prefix distinguishes variables that are being _bound_ from variables that are being _used_, and `{ ... }` blocks delimit where bindings are in scope:

```
a + b  // the variable a is being used
$a = b // the variable a is being bound
```

Blocks are syntactic sugar for anonymous functions, whose parameters are determined statically by the explicit bindings that appear to their left. The block `{ x }` in `Pair($x, $y) => { x }` is desugared to `(x) => (y) => x`. Recursive functions use `$$` for double bindings (available both inside the function body and in the enclosing scope):

```
{
    $$factorial($n) = {
        if(eq(n, Zero), { One }, { times(n, factorial(minus(n, One))) })
    }
    factorial(Five)
}
```

When a function is called with explicit bindings, the system automatically wraps the arguments so the function can observe their syntactic structure. A call like `Pair($x, "y")` is annotated as `Call(Value(Pair), Binding("x"), Value("y"))`, preserving the distinction between bindings and values. A call without any bindings, like `Pair(a, b)`, is left unevaluated and can be freely optimized.

This works, but it ends up looking verbose, because every variable binding has to be annotated with `$` or `$$`. In most languages, whether a name is a binding or a reference is already clear from its position. In `x = "hello"`, the `x` on the left of `=` is _obviously_ a binding. Writing `$x = "hello"` is redundant.

### Implicit bindings (the [`implicit/`](implicit/) variant)

The implicit variant eliminates markers entirely by determining bindings from syntactic position. The core insight is that binding context is almost always determined by position relative to two syntactic elements: _infix operators_ and _`{ ... }` blocks_.

Names on the left-hand side of an infix expression are _bound_ when:

- The right-hand side is a `{ ... }` block: `Pair(x, y) => { body }` (The names `x` and `y` in the pattern are bindings, scoped to the block. This is called an _argument scope_.)
- The expression appears as an element of an enclosing `{ ... }` block: `{ x = "hello", f(x) }` (The name `x` is a binding, scoped to the rest of the block. This is called an _enclosing scope_.)

Uppercase names (`Pair`, `True`) are always literal constructors, never bindings. Lowercase names in binding context become bindings; outside binding context they are variable references.

Elixir's `^` pin operator provides the escape hatch for the reverse direction: when a name _would_ be a binding by position, `^` forces it to resolve from the outer scope instead:

```
{
    y = Bar
    match(Pair(Foo, Bar), [Pair(x, ^y) => { x }])
}
// ^y matches against the value Bar from the outer scope
// result: Foo
```

Function definitions use a _trailing block_ syntax: `name = (params) { body }`. The `{ ... }` block follows the infix expression as an additional argument, and the function name is available inside its own body for recursion:

```
{
    factorial = (n) {
        if(eq(n, Zero), { One }, { times(n, factorial(minus(n, One))) })
    }
    factorial(Five)
}
```

A name is available in _both_ its own body and the enclosing scope only when an infix expression in a block has a trailing `{ ... }` block. Double binding is tied specifically to the trailing block syntax, keeping it visually unambiguous.

- `f = (x, y) { body }` in a block: `f` is double-bound (recursive in `body`, available after)
- `x = "hello"` in a block: `x` is bound in the enclosing scope only (no recursion)
- `Pair(x, y) => { body }`: `x` and `y` are bound in the argument scope only

The case `f = { body }` as a direct block element (which combines an enclosing-scope binding with an argument-scope block) is _rejected_ by the parser in the current implementation. Whether this should produce a double binding or not is left an open question and rejecting it preserves backwards compatibility for when a decision is made.

Unlike the explicit variant, where `$` markers could appear anywhere (including in prefix call arguments), implicit bindings only arise in infix expressions. Prefix calls like `if(cond, { then }, { else })` are always regular function calls. Blocks in prefix arguments are thunks, never binding scopes. This is by design: all binding constructs must use infix syntax, which makes binding context unambiguous from the shape of the expression alone.

## Pattern matching as a library

Pattern matching with unification is implemented as a library, without extending the language or adding any built-in support for matching. The language desugars entirely to a call-by-value lambda calculus with a handful of built-in functions (`=`, `if`, `eq`, `tag`, `fields`, `head`, `tail`, `is_empty`, `cons`, `fix`, `panic`). In contrast to these built-in functions, pattern matching is user-defined: The `match` function and the `=>` infix operator are regular user-defined functions that process the annotated syntax tree at runtime.

```
match(Pair(Foo, Bar), [
    Pair(x, y) => { Pair(y, x) }
])
// result: Pair(Bar, Foo)

match(Pair(Foo, Foo), [Pair(x, x) => { x }])
// result: Foo

match(Pair(Foo, Bar), [
    Pair(x, x) => { Unified(x) }
    Pair(a, b) => { Distinct(a, b) }
])
// result: Distinct(Foo, Bar)
```

Pinning resolves a variable from the enclosing scope instead of creating a binding:

```
{
    y = Baz
    match(Pair(Foo, Bar), [
        Pair(x, ^y) => { FoundIt(x) }
        z => { Fallback(z) }
    ])
}
// ^y is Baz, which doesn't match Bar
// result: Fallback(Pair(Foo, Bar))
```

Nested patterns, tag-based dispatch, wildcard arms, and literal arms all work:

```
match(Just(Pair(Foo, Bar)), [
    Just(Pair(x, y)) => { Pair(y, x) }
])
// result: Pair(Bar, Foo)

match(Left(Foo), [
    Right(x) => { GotRight(x) }
    Left(x) => { GotLeft(x) }
])
// result: GotLeft(Foo)
```

## Limitations and open questions

- **Block-RHS in blocks is rejected.** The syntax `{ f = { body }, rest }` is currently a validation error. It's unclear whether `f` should be double-bound (recursive, like the trailing block case) or single-bound (consumed by the block only). Rejecting it preserves the option to decide later.
- **No prefix-level macros.** The explicit variant allowed macro calls like `f($x, { x })` where `$` markers in prefix arguments triggered annotated desugaring. The implicit variant restricts bindings to infix expressions, which means some patterns expressible in the explicit system cannot be written here. Whether this is a real limitation in practice is an open question.
- **Pin is only useful in binding context.** Outside binding context, `^x` is equivalent to `x`. The pin operator could be restricted to binding context only, but allowing it everywhere simplifies the implementation without causing harm.
- **Pattern annotations are runtime values.** The desugarer wraps patterns in `Binding(...)`, `Value(...)`, and `Call(...)` tags, which the `match` prelude function inspects at runtime. A more sophisticated implementation could statically analyze patterns, but runtime inspection is sufficient for this experiment and keeps the language minimal.

## Related work

- [**Kernel**](https://web.cs.wpi.edu/~jshutt/dissertation/etd-090110-124904-Shutt-Dissertation.pdf) — Shutt's Kernel language distinguishes _operatives_ (which receive unevaluated arguments) from _applicatives_ (which evaluate their arguments). The approach here is a deliberate restriction of Kernel-style operatives: evaluation behavior is determined syntactically rather than by runtime type checking.
- [**Mitchell (1993)**](https://www.sciencedirect.com/science/article/pii/0167642393900049/pdf) and [**Wand (1998)**](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=dc9cdd51c6e02c45ab267c9973e5c4af9fb11e44) — foundational work on the observation that the ability to observe syntactic structure (as in fexprs) conflicts with equational reasoning. Both variants address this by ensuring that syntactic structure is only observable in specific, syntactically determined positions.
- [**Hygienic macros**](https://en.wikipedia.org/wiki/Hygienic_macro) — traditional macro systems ensure that macro expansions do not capture variables unintentionally. Both variants sidestep the problem by making all binding sites syntactically visible, so there is no separate macro expansion phase that could introduce unintended captures.
- [**Elixir pin operator**](https://hexdocs.pm/elixir/main/patterns-and-guards.html#variables) — Elixir uses `^x` in patterns to resolve a variable from the outer scope rather than binding a fresh one. The implicit variant adopts the same convention.

## Notes

- [Custom binding constructs without macros, part 1: explicit bindings](https://fredkettelhoit.com/notes/2025-03-16.html)
- [Custom binding constructs without macros, part 2: desugaring bindings](https://fredkettelhoit.com/notes/2025-03-22.html)
- [Reasonable macros](https://fredkettelhoit.com/notes/2025-04-20.html)
- [Reasonable macros through explicit bindings, part 2](https://fredkettelhoit.com/notes/2025-08-05.html)
- [Reasonable macros through explicit bindings, part 3](https://fredkettelhoit.com/notes/2025-08-29.html)
- [Implicit vs. explicit macro bindings for recursive definitions](https://fredkettelhoit.com/notes/2026-01-30.html)
