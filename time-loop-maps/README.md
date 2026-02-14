# Time loop maps - programming with paradoxical loop values

A minimal language / calculus for exploring paradoxical fixed points, which are values that are both X and not X, so that paradoxes can be solved. Think of it like solving time travel paradoxes by going back in time and not going back in time, at the same time.

## Motivation

Most recursive functions have well-behaved fixed points, meaning values `v` where `f(v) == v`. The function `f(x) = 'foo'` has `'foo'` as its fixed point (trivially). Even something like `f(x) = if x == 'foo' then 'foo' else 'foo'` is easy, because the fixed point is again just `'foo'`, since `f('foo') == 'foo'`.

But some functions are “adversarial”. Here'es an example:

```py
def f(x):
    if x == 'foo':
        'bar'
    else:
        'foo'
```

No ordinary value satisfies `f(v) == v` here: whatever you feed in, the function returns the other thing. This structure mirrors the liar's paradox (“this statement is false”) and underlies the proof of the halting problem: we can always construct a function that does the opposite of whatever we predict.

But what if we _extended_ the language with values that can represent this oscillation directly? Instead of saying “there is no fixed point,” what if we described the paradox itself as a value?

## Outcome

The code implements a small calculus that can solve paradoxical fixed points for fixed sets of values (in other words fixed points that oscillate between a finite set of values, but not fixed points that grow infinitely, like `'x'`, `['x']`, `[['x']]`, etc.).

The central idea is **time loop maps**: values that simultaneously occupy multiple states, written `('x' & 'y')`. Rather than treating the liar's paradox as a dead end, we model it as a stable oscillation between `'x'` and `'y'`.

Here's an example of what we can “solve” paradoxically:

```py
if v == 'x':
    'y'
else:
    'x'
```

The expression above has no standard fixed point (a value `v` where `v` equals `f(v)`) since it turns `'x'` into `'y'` and `'y'` into `'x'`. Time loop calculus solves this by introducing "time loop" values that represent oscillating superpositions of values.

The value `('x' & 'y')` represents a time loop: a value that is simultaneously both `'x'` and `'y'`, oscillating between them. Internally, this is stored as a map `('x': 'x', 'y': 'y')` where keys track the origin of each value. This map-based representation allows us to find fixed points for paradoxical functions like the liar's paradox.

When comparing a time loop to an atomic value, the comparison is lifted across all entries in the map. So `('x' & 'y') == 'x'` evaluates to `('x': true, 'y': false)`, creating a mapped boolean structure that can be applied to conditionals.

For nested paradoxes, time loops can contain other time loops. The value `('y' & ('x' & 'y'))` has rank 2, where rank-based lifting ensures that comparisons maintain compositional reasoning. When comparing values of different ranks, the lower-rank value is lifted into the structure of the higher-rank value.

After evaluating an expression, the resulting map is normalized: if the keys and values form a cycle (the same set, just reordered), the map is transformed so each key maps to itself, giving us a true fixed point.

All time loops share synchronized evaluation, allowing multiple subexpressions that depend on the same fixed point to remain consistent through map key alignment.

Here are a few examples with their paradoxical fixed points:

### Simple identity

```
if 'x' == 'x':
    'x'
else:
    'y'
```

**Fixed point:** `'x'`

### Simple liar

```
if ('x' & 'y') == 'x':
    'y'
else:
    'x'
```

**Fixed point:** `('x' & 'y')`

The comparison produces `('x': true, 'y': false)`, which selects 'y' for the 'x' case and 'x' for the 'y' case, yielding `('x': 'y', 'y': 'x')`. After normalization, this becomes `('x': 'x', 'y': 'y')`, our original value.

### Captured liar

```
if ('y' & ('x' & 'y')) == ('x' & 'y'):
    'y'
else:
    'x'
```

**Fixed point:** `('y' & ('x' & 'y'))`

The nested structure (rank 2) is compared with a rank 1 value through lifting, and after evaluation and normalization, returns to the original value.

### Escaped liar

```
if ('x' & ('x' & 'y')) == ('x' & 'y'):
    'x'
else:
    if ('x' & ('x' & 'y')) == 'x':
        'y'
    else:
        'x'
```

**Fixed point:** `('x' & ('x' & 'y'))`

The nested conditionals interact through rank-based lifting, and the synchronized evaluation ensures consistent behavior across both comparisons.

### Liar's twin

```
if ('x' & 'y') == 'x':
    'y'
else:
    if ('x' & 'y') == 'x':
        'z'
    else:
        'x'
```

**Fixed point:** `('x' & 'y')`

Both conditionals see the same map `('x': true, 'y': false)`, so the evaluation is synchronized. The middle branch ('z') is never visited because both conditions align through the shared map keys.
