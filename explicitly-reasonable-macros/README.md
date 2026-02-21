# Explicitly reasonable macros — pattern matching as a library

Can a language allow everything to be redefined (including variable assignment and pattern matching) while keeping the scope of variables immediately obvious, without evaluating any function or macro?

This experiment implements a minimal language where pattern matching with unification is defined entirely as a library (without any built-in support for matching) by making variable bindings syntactically explicit. The `$` prefix distinguishes variables that are being _bound_ from variables that are being _used_, and `{ ... }` blocks delimit where bindings are in scope. These two syntactic markers are enough for the language to automatically preserve the structure of expressions containing bindings, so that a user-defined `match` function can inspect patterns, extract bindings, and perform unification at runtime (all while variable scopes remain statically obvious).

## Motivation

Programming languages face a tension between the ability to extend them dynamically and the ability to reason about them statically. Constructs that _bind variables_, such as function definitions or pattern matching, are usually a fixed part of a language's core syntax, unless we go for Lisp-like macros, which are powerful but hard to reason about.

The problem with macros is that just seeing an expression such as `f(2 + 2)` in the source code does not guarantee that it is equivalent to `f(4)`, because `f` could be a macro and thus treat `2 + 2` differently from `4`. By exposing all of the syntactic structure of a program, macros have to be used sparingly and/or expanded before it is possible to reason about equivalent expressions.

There is an unexplored middle ground, however, of allowing binding constructs to be defined and extended, while ensuring that all variables are lexically bound and that their scope can be determined statically. This experiment explores that middle ground, while respecting a single guiding principle:

_Every construct in the language can be redefined, there are no privileged language constructs. But the scope of variables remains immediately obvious, just by looking at the source code, without evaluating any function or macro._

## Approach

The core idea is to make _bindings explicit._ Most languages do not visually distinguish between bound variables that are _used_ and fresh variables that are being _bound:_

```
a + b // the variable a is being used
a = b // the variable a is being bound
```

In the first case, `a` is looked up in the current scope, whereas in the second case, `a` is a fresh variable that will be bound. That they play such different roles is not visible just by looking at the variables, nor by looking at the operators, because `+` and `=` are both infix symbols.

We distinguish these two cases by prefixing bindings with `$`:

```
a + b  // the variable a is being used
$a = b // the variable a is being bound
```

### Explicit scopes

The scope of variables is made explicit using `{ ... }` blocks. There are two types of macro scopes, an _enclosing_ scope and an _argument_ scope:

```
// enclosing scope: $x is bound for the rest of the { ... } block
{
    $x = "hello"
    foo(x)
}

// argument scope: $x is bound inside the { ... } argument
Pair($x, $y) => {
    x
}
```

Blocks are syntactic sugar for anonymous functions, whose parameters are determined statically by the explicit bindings that appear to their left. The block `{ x }` in `Pair($x, $y) => { x }` is desugared to `(x) => (y) => x`. The number of lambda parameters equals the number of bindings — even `Pair($x, $x) => { x }` desugars to two nested lambdas, since there are two binding occurrences.

### Double bindings

Recursive function definitions need the function name to be available both inside its own body (for recursive calls) and in the surrounding scope (so we can call it later). The `$$` prefix marks a binding that is consumed in both scopes:

```
{
    $$factorial($n) = {
        if(eq(n, Zero), { One }, { times(n, factorial(minus(n, One))) })
    }
    factorial(Five)
}
```

### How macros see structure

When a function is called with explicit bindings, the system automatically wraps the arguments so the function can observe their syntactic structure. A call like `Pair($x, "y")` is annotated as `Call(Value(Pair), Binding("x"), Value("y"))`, preserving the distinction between bindings and values. A call without any bindings, like `Pair(a, b)`, is left unevaluated and can be freely optimized.

This is the key insight: it is _syntactically_ clear when and where evaluation happens. A compiler can safely optimize any expression that does not contain explicit bindings. Making bindings explicit is only a slight departure from traditional syntax, but unlocks most of the common uses of macros without introducing a full-blown macro system.

## Outcome: pattern matching as a library

The experiment implements a working scanner, parser, desugarer, and interpreter. The language desugars entirely to a call-by-value lambda calculus with a handful of built-in functions (`=`, `if`, `eq`, `tag`, `fields`, `head`, `tail`, `is_empty`, `cons`, `fix`, `panic`).

The central result is that **pattern matching with unification is implemented as a library**, without extending the language or adding any built-in support for matching. The `match` function and the `=>` infix operator are regular user-defined functions that process the annotated syntax tree at runtime:

```
match(Pair(Foo, Bar), [
    Pair($x, $y) => { Pair(y, x) }
])
// result: Pair(Bar, Foo)
```

Unification — requiring repeated bindings to match equal values — works naturally:

```
match(Pair(Foo, Foo), [Pair($x, $x) => { x }])
// result: Foo

match(Pair(Foo, Bar), [
    Pair($x, $x) => { Unified(x) }
    Pair($a, $b) => { Distinct(a, b) }
])
// result: Distinct(Foo, Bar)
```

Matching against values from the enclosing scope (rather than bindings) also works, because variables without a `$` prefix are evaluated before being passed to the match function:

```
{
    $y = Bar
    match(Pair(Foo, Bar), [Pair($x, y) => { x }])
}
// result: Foo
```

Nested patterns, tag-based dispatch, wildcard arms, and literal arms all work:

```
match(Just(Pair(Foo, Bar)), [
    Just(Pair($x, $y)) => { Pair(y, x) }
])
// result: Pair(Bar, Foo)

match(Left(Foo), [
    Right($x) => { GotRight(x) }
    Left($x) => { GotLeft(x) }
])
// result: GotLeft(Foo)
```

The full pattern matching implementation is roughly 40 lines and is loaded as a prelude — it uses only the built-in functions listed above and defines `match` as a recursive function that walks the annotated pattern tree.

## Related work

- [**Kernel**](https://web.cs.wpi.edu/~jshutt/dissertation/etd-090110-124904-Shutt-Dissertation.pdf) — Shutt's Kernel language distinguishes _operatives_ (which receive unevaluated arguments) from _applicatives_ (which evaluate their arguments). The approach here is a deliberate restriction of Kernel-style operatives: evaluation behavior is determined syntactically by binding markers rather than by runtime type checking.
- [**Mitchell (1993)**](https://www.sciencedirect.com/science/article/pii/0167642393900049/pdf) and [**Wand (1998)**](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=dc9cdd51c6e02c45ab267c9973e5c4af9fb11e44) — foundational work on the observation that the ability to observe syntactic structure (as in fexprs) conflicts with equational reasoning. Explicit bindings address this by ensuring that syntactic structure is only observable where binding markers are present (all other expressions can be freely substituted).
- [**Hygienic macros**](https://en.wikipedia.org/wiki/Hygienic_macro) — traditional macro systems ensure that macro expansions do not capture variables unintentionally. Explicit bindings sidestep the problem by making all binding sites syntactically visible, so there is no separate macro expansion phase that could introduce unintended captures.
- [**Elixir pin operator**](https://hexdocs.pm/elixir/main/patterns-and-guards.html#variables) — Elixir uses `^x` in patterns to resolve a variable from the outer scope rather than binding a fresh one. The explicit `$x` binding marker serves an analogous role in reverse: unmarked variables are resolved, marked variables are bound.

## Notes

- [Custom binding constructs without macros, part 1: explicit bindings](https://fkettelhoit.com/notes/2025-03-16.html) (2025-03-16)
- [Custom binding constructs without macros, part 2: desugaring bindings](https://fkettelhoit.com/notes/2025-03-22.html) (2025-03-22)
- [Reasonable macros](https://fkettelhoit.com/notes/2025-04-20.html) (2025-04-20)
- [Reasonable macros through explicit bindings, part 2](https://fkettelhoit.com/notes/2025-08-05.html) (2025-08-05)
- [Reasonable macros through explicit bindings, part 3](https://fkettelhoit.com/notes/2025-08-29.html) (2025-08-29)
- [Implicit vs. explicit macro bindings for recursive definitions](https://fkettelhoit.com/notes/2026-01-30.html) (2026-01-30)
