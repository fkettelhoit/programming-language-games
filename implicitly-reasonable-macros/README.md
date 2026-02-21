# Implicitly reasonable macros — pattern matching as a library, without binding markers

Can a language allow everything to be redefined (even variable assignment and pattern matching) while keeping the scope of variables immediately obvious, _without_ explicit bindings?

This experiment implements a minimal language where pattern matching with unification is defined entirely as a library (without any built-in support for matching) by determining variable bindings _implicitly_ from syntactic position. There are no `$` markers: Whether a name is being _bound_ or _used_ is determined solely by where it appears in the expression. A `^` prefix ("pin") resolves a variable from the outer scope in positions that would otherwise create a binding.

This is a direct successor to the [explicitly-reasonable-macros](../explicitly-reasonable-macros/) experiment, which achieved the same result but required `$` and `$$` prefixes on all binding sites. The experiment here shows that those markers can be eliminated entirely while preserving the same guarantees about lexical scope.

## Motivation

Programming languages face a tension between the ability to extend them dynamically and the ability to reason about them statically. Constructs that _bind variables_, such as function definitions or pattern matching, are usually a fixed part of a language's core syntax, unless we go for Lisp-like macros, which are powerful but hard to reason about.

The [explicitly-reasonable-macros](../explicitly-reasonable-macros/) experiment implemented macros as simple syntactic sugar with obvious static scopes and explicit bindings. It worked, but it ended up looking pretty verbose, because every variable binding hat to be annotated with `$` or `$$`. But in most other languages, whether a name is a binding or a reference is already clear from its position. In `x = "hello"`, the `x` on the left of `=` is _obviously_ a binding. Writing `$x = "hello"` is redundant.

Can we get the same benefits (user-definable binding constructs with statically obvious scope) by relying entirely on syntactic position, removing the need for explicit markers?

## Approach

The core insight is that binding context is almost always determined by position relative to two syntactic elements: _infix operators_ and _`{ ... }` blocks_.

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

Unlike the explicit-binding experiment, where `$` markers could appear anywhere (including in prefix call arguments), implicit bindings only arise in infix expressions. Prefix calls like `if(cond, { then }, { else })` are always regular function calls. Blocks in prefix arguments are thunks, never binding scopes. This is by design: all binding constructs must use infix syntax, which makes binding context unambiguous from the shape of the expression alone.

## Outcome: pattern matching as a library

The experiment implements a working scanner, parser, validation pass, desugarer, and interpreter. The language desugars entirely to a call-by-value lambda calculus with a handful of built-in functions (`=`, `if`, `eq`, `tag`, `fields`, `head`, `tail`, `is_empty`, `cons`, `fix`, `panic`).

As in the explicit experiment, **pattern matching with unification is implemented as a library**, without extending the language or adding any built-in support for matching. But now without any `$` markers:

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

Implicit bindings are more ergonomic and closer to conventional syntax, but require the reader to understand the positional rules and use `^` to opt out. Both experiments share the same fundamental principle (variable scope is statically obvious without evaluating any function) but they realize it differently.

## Limitations and open questions

- **Block-RHS in blocks is rejected.** The syntax `{ f = { body }, rest }` is currently a validation error. It's unclear whether `f` should be double-bound (recursive, like the trailing block case) or single-bound (consumed by the block only). Rejecting it preserves the option to decide later.
- **No prefix-level macros.** The explicit experiment allowed macro calls like `f($x, { x })` where `$` markers in prefix arguments triggered annotated desugaring. The implicit experiment restricts bindings to infix expressions, which means some patterns expressible in the explicit system cannot be written here. Whether this is a real limitation in practice is an open question.
- **Pin is only useful in binding context.** Outside binding context, `^x` is equivalent to `x`. The pin operator could be restricted to binding context only, but allowing it everywhere simplifies the implementation without causing harm.
- **Pattern annotations are runtime values.** The desugarer wraps patterns in `Binding(...)`, `Value(...)`, and `Call(...)` tags, which the `match` prelude function inspects at runtime. A more sophisticated implementation could statically analyze patterns, but runtime inspection is sufficient for this experiment and keeps the language minimal.

## Related work

- [**Kernel**](https://web.cs.wpi.edu/~jshutt/dissertation/etd-090110-124904-Shutt-Dissertation.pdf) — Shutt's Kernel language distinguishes _operatives_ (which receive unevaluated arguments) from _applicatives_ (which evaluate their arguments). The approach here is a deliberate restriction of Kernel-style operatives: evaluation behavior is determined syntactically by position rather than by runtime type checking.
- [**Mitchell (1993)**](https://www.sciencedirect.com/science/article/pii/0167642393900049/pdf) and [**Wand (1998)**](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=dc9cdd51c6e02c45ab267c9973e5c4af9fb11e44) — foundational work on the observation that the ability to observe syntactic structure (as in fexprs) conflicts with equational reasoning. Implicit bindings address this by ensuring that syntactic structure is only observable in specific, syntactically determined positions.
- [**Hygienic macros**](https://en.wikipedia.org/wiki/Hygienic_macro) — traditional macro systems ensure that macro expansions do not capture variables unintentionally. Implicit bindings sidestep the problem by making all binding sites positionally determined, so there is no separate macro expansion phase that could introduce unintended captures.
- [**Elixir pin operator**](https://hexdocs.pm/elixir/main/patterns-and-guards.html#variables) — Elixir uses `^x` in patterns to resolve a variable from the outer scope rather than binding a fresh one. This experiment adopts the same convention: bare names in binding context are bindings, `^x` resolves from the enclosing scope.
- [**Explicitly reasonable macros**](../explicitly-reasonable-macros/) — the direct predecessor to this experiment. Uses `$x` markers instead of positional binding, achieving the same pattern-matching-as-a-library result with different ergonomic trade-offs.

## Notes

- [Custom binding constructs without macros, part 1: explicit bindings](https://fkettelhoit.com/notes/2025-03-16.html) (2025-03-16)
- [Custom binding constructs without macros, part 2: desugaring bindings](https://fkettelhoit.com/notes/2025-03-22.html) (2025-03-22)
- [Reasonable macros](https://fkettelhoit.com/notes/2025-04-20.html) (2025-04-20)
- [Reasonable macros through explicit bindings, part 2](https://fkettelhoit.com/notes/2025-08-05.html) (2025-08-05)
- [Reasonable macros through explicit bindings, part 3](https://fkettelhoit.com/notes/2025-08-29.html) (2025-08-29)
- [Implicit vs. explicit macro bindings for recursive definitions](https://fkettelhoit.com/notes/2026-01-30.html) (2026-01-30)
