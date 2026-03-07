# Symbiotic effect handling — Let the host do your math

How can you jump-start a programming language? What if instead of building your own standard library you just “symbiotically” depend on a host even for basic operations like arithmetic?

## Motivation

The idea of relying on a host ecosystem isn't exactly new, many languages have been designed with interop in mind, for example embedded languages like Lua or languages targeting existing VMs like Clojure or Scala. But these languages still build a lot of functionality into their own standard libraries, because interacting with the host language or VM can feel foreign. What if a language were designed to do as little as possible, and just yield control back to the host whenever it needs to do anything non-trivial?

The word “yield” gives away the main implementation idea: rely as much as possible on coroutines / continuations that can _yield_ execution back to the host, suspending the call stack of the symbiotic guest as a result. The host effectively acts as an _effect handler_ which can handle the effect raised by the coroutine (or decide not to) and then resume where the guest left off (or decide not to).

## Outcome

The experiment implements a lightweight stack-based virtual machine that can be suspended and resumed cooperatively between guest and host. An effect that is raised within the VM can either be caught and handled by an effect handler defined in the guest language, or bubble up to the host, in which case the continuation wraps the entire state and call stack of the virtual machine.

Any variable ending with `!` is treated as an effect and resolved _dynamically_ depending on which effect handlers are on the effect handler stack (or ultimately by the host language) when the effect is raised by being called:

```
try {
    x = read!("file.txt")
    x + 1
} catch: [
    read!: (resume, path) => { resume(41) }
]
// result: 42
```

Each effect handler catches a specific effect by name and handles it using an anonymous function that receives a continuation (which can resume the code at the point where the effect was raised) and the argument(s) with which the effect was called.

### Mutable state through effects

Because effect handlers have access to the continuation, they can implement patterns like mutable state without any built-in mutation support:

```
run_state = (state, thunk) {
    try { thunk() } catch: [
        get!: (resume) => { run_state(state, { resume(state) }) }
        set!: (resume, new_state) => { run_state(new_state, { resume(Unit) }) }
    ]
}

run_state(0, { set!(42), get!() })
// result: 42
```

### Symbiotic arithmetic

When an effect bubbles up to the host without being caught by a guest handler, the host can handle it. This makes it possible to offload even core operations like arithmetic to the host. A factorial function using built-in arithmetic:

```
factorial = (n) {
    if(n == 0, { 1 }, { n * factorial(n - 1) })
}
```

The same function using symbiotic host-handled arithmetic:

```
factorial = (n) {
    if(eq!(n, 0), { 1 }, { mul!(n, factorial(sub!(n, 1))) })
}
```

In both cases `factorial(10)` evaluates to `3628800`. The symbiotic version raises `eq!`, `mul!`, and `sub!` as effects that bubble up to the host (here a Rust program), which handles the arithmetic and resumes the VM with the result.

### Benchmarking: how expensive is symbiotic effect handling?

To test how feasible it is to offload core operations to the host, the same algorithms (factorial, fibonacci, sum) are implemented in four ways:

- **Pure Rust** — baseline, no VM overhead.
- **Built-in** — arithmetic as VM bytecode instructions (`+`, `-`, `*`, etc.).
- **Host-handled** — arithmetic through effects (`add!`, `sub!`, `mul!`, etc.), handled by the Rust host.
- **Peano** — natural numbers encoded as algebraic data types (`Z`, `S(Z)`, `S(S(Z))`, ...), entirely within the guest language.

In initial micro benchmarks, using host interop to handle arithmetic takes about twice the time as using built-in arithmetic instructions, while Peano arithmetic is 1000 times slower or worse. Taking twice the time is not great, but it's a decent start and could make it viable to implement arithmetic fully through the host if numeric performance isn't the primary goal of the language.

### Multi-shot continuations

Continuations are one-shot by default (consumed when resumed), but can be cloned to create multi-shot continuations. In Rust, this comes down to cloning the entire VM. Not the most efficient, but good enough for a first version:

```rust
match run_program(&program).unwrap() {
    VMResult::Effect { continuation, .. } => {
        let r1 = continuation.clone().resume(Value::Int(3)).unwrap();
        let r2 = continuation.resume(Value::Int(7)).unwrap();
        // r1 = 30, r2 = 70
    }
    // ...
}
```

## Related Work

- [**Koka**](https://koka-lang.github.io/koka/doc/book.html#why-handlers) — the direct inspiration for effect handlers and the “minimal but general” design goal.
- [**Lua**](https://www.lua.org/) — the most well-known example of an embeddable language designed to be hosted, though Lua still builds significant functionality into its own standard library rather than delegating to the host.

## Notes

- [Symbiotic effect handling](https://fredkettelhoit.com/notes/2026-02-22.md)
- [Layered programming, symbiotic programming](https://fredkettelhoit.com/notes/2025-08-30.md)
