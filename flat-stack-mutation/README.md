# Flat stack mutation - Functional-but-in-place mutation on the stack

With references that only point backwards on the stack, uniqueness (and mutation) checking becomes a linear walk on the stack.

## Motivation

A functional programming language can safely mutate values under the hood if the mutation cannot be observed by anyone else. In a virtual machine with references that can only point to older values on the stack, a value can be safely mutated if there's a single unique reference to it, which can be decided by scanning the stack region between the current reference and the origin of the value.

## Outcome

The approach isn't practical in its current form.

While the linear walk works for deciding uniqueness and mutating functionally-but-in-place, many programs that are `O(n)` in other languages end up being `O(n^2)` in the prototyped VM because the linear uniqueness check has to walk a linearly growing region of the stack on every iteration.

The experiment contains basic benchmarks that compare the flat stack VM to a simple cons-based VM baseline. While the flat VM wins for programs that involve a lot of random access, it loses significantly on other benchmarks where a cons-based VM remains linear instead of becoming quadratic.
