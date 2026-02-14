# Minimal modern syntax — lispy minimalism meets prefix/infix/keyword calls

Can a language be as minimal and general as Lisp (where control structures like `if`, `match`, and `let` are just ordinary functions) while using far fewer parentheses and feeling familiar to programmers coming from C/JS-style languages?

## Motivation

Lisp achieves generality by making everything a macro or function call, but the cost is a uniform, deeply nested parenthesized syntax that obscures the visual structure of programs. The hypothesis here is that three complementary call styles (prefix `f(a, b)`, infix `a f b`, and keyword `f(a) else { ... }`) can cover the ground that Lisp covers with S-expressions, while remaining visually legible and requiring no privileged built-in syntax for conditionals, pattern matching, or variable binding.

## Outcome

The experiment implements a working scanner, parser, and pretty-printer for the proposed syntax:

```swift
add = (x, y) {
    x + y
}

match_pair = (x) {
    match (x) [
        Foo(Bar, Baz) -> {
            "just Foo(Bar, Baz)"
        }
        Foo(x, x) -> {
            twice(x)
        }
        Foo(x, ^y) -> {
            "second element is y"
        }
        _ -> {
            throw!("Expected a Foo(...)!")
        }
    ]
}

side_effect()

do_something = () {
    input = read!()
    match (input) [
        Ok(contents) -> {
            contents
        }
        _ -> {
            throw!("Couldn't read any input!")
        }
    ]
}

try {
    something_that_might_read()
} catch: read! as: (resume, arg) => {
    resume("test input")
}
```

None of `match`, `->`, `if`, `=`, `try`, `catch`, or `else` are built-in syntax. Instead, they are ordinary identifiers that the parser treats uniformly. The pretty-printer enforces consistent formatting and can serve as an autoformatter.

An unintended but welcome side effect of having both a lightweight syntax for tags (strings starting with uppercase letters that don't need double quotes) and trailing arguments is that these features naturally lead to a decent data syntax without any additional work for the parser or pretty-printer:

```swift
some_data = [
    Html lang: "en" stylesheet: "styles/style.css" title: "Page Title" sections: [
        Note date: ["2025", "06", "12"]
        Section title: "Section 1" blocks: [
            ["This is a paragraph with ", Emph("emphasis")]
            List [
                [
                    "An item with a "
                    Link("link") href: "http://www.example.com"
                ]
            ]
            Subsection title: "Subsection Title" blocks: [
                ["Another paragraph."]
                ["Another paragraph."]
            ]
        ]
        Section title: "Section 2" id: "sec2" blocks: [["Not much here."]]
    ]
]
```

- **Trailing arguments**: `[...]` and `{...}` can follow a call outside the parentheses, so `f(a) { x }` desugars to `f(a, { x })`.
- **Keyword arguments**: when a bare variable follows a trailing argument, it is parsed as a keyword and collected into a list, so `if (c) { t } else: { f }` desugars to `if(c, { t }, [["else", { f }]])`.
- **Infix calls**: `a f b` desugars to `f(a, b)`; chaining the same operator (`a + b + c`) is allowed without extra parentheses, but mixing operators always requires explicit grouping.
- **Tuples vs. grouping**: `(x, y)` is a two-element tuple; `(x)` is treated as plain grouping in infix position.
- **Tags**: identifiers starting with an uppercase letter (e.g. `Foo`, `Ok`) are string-interned atomic values.

## Dead Ends

**Keywords without colons.** An early design used bare identifiers as keywords without a trailing `:`, giving syntax like `do { ... } while { ... }`. This is more familiar from C-family languages, but creates an irresolvable ambiguity: `f(x) g h(y)` could be either the infix expression `g(f(x), h(y))` or a keyword call where `g` is a keyword argument to `f`. The colon form `catch: e as: handler` is explicit enough to eliminate the ambiguity, allows infix expressions as keyword values without extra parentheses, and generalises to a key-value syntax useful beyond control structures.

**`[...]` for anonymous function parameters.** An early version used `[x, y] => f(x, y)` for multi-argument anonymous functions, reserving `(...)` purely for grouping and call syntax. This was dropped when `(...)` was extended to carry tuple semantics: `(x, y) => f(x, y)` is now a function whose parameter is a two-element tuple, and `x => f(x)` handles the single-argument case without any list syntax.

**Allowing composite expressions as infix operators.** Requiring the operator in an infix call to always be a plain variable (never a computed expression) could be considered overly restrictive, but it is what makes keyword-call disambiguation possible: if the token after a call is a variable, it is either the start of an infix expression or a keyword, and the colon suffix on keywords removes all ambiguity.

## Related Work

- [**Sweet Expressions (SRFI-110)**](https://readable.sourceforge.io/) — adds indentation-sensitive and infix-friendly syntax on top of S-expressions in Lisp, the closest precedent for "fewer parentheses, same generality".
- [**Koka**](https://koka-lang.github.io/koka/doc/book.html#why-mingen) — the direct inspiration for trailing `{...}` arguments and the "minimal but general" design goal; Koka's effect system is also relevant to the `try`/`catch` examples above.
- [**Elixir keyword lists and do-blocks**](https://hexdocs.pm/elixir/main/optional-syntax.html) — the inspiration for keyword arguments; Elixir's `do:` / `else:` desugaring is essentially the same mechanism with slightly different surface syntax.
- [**Uniform Function Call Syntax**](https://en.wikipedia.org/wiki/Uniform_Function_Call_Syntax) — could extend the syntax implemented here with piped calls (`a.f(b)` as sugar for `f(a, b)`), which would remove the need for an infix pipe operator
