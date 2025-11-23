# Time loop calculus

A minimal language / calculus for exploring paradoxical fixed points.

```py
if v == 'x':
    'y'
else:
    'x'
```

The function above has no standard fixed point (a value `v` where `v` equals `f(v)`) since it turns 'x' into 'y' and 'y' into 'x'. Time loop calculus solves this by introducing "time loop" values that represent oscillating superpositions of values.

The value `('x' & 'y')` represents a time loop—a value that is simultaneously both 'x' and 'y', oscillating between them. Internally, this is stored as a map `('x': 'x', 'y': 'y')` where keys track the origin of each value. This map-based representation allows us to find fixed points for paradoxical functions like the liar's paradox.

When comparing a time loop to an atomic value, the comparison is lifted across all entries in the map. So `('x' & 'y') == 'x'` evaluates to `('x': true, 'y': false)`, creating a mapped boolean structure that can be applied to conditionals.

For nested paradoxes, time loops can contain other time loops. The value `('y' & ('x' & 'y'))` has rank 2, where rank-based lifting ensures that comparisons maintain compositional reasoning. When comparing values of different ranks, the lower-rank value is lifted into the structure of the higher-rank value.

After evaluating an expression, the resulting map is normalized: if the keys and values form a cycle (the same set, just reordered), the map is transformed so each key maps to itself, giving us a true fixed point.

All time loops share synchronized evaluation, allowing multiple subexpressions that depend on the same fixed point to remain consistent through map key alignment.

Here are a few examples:

## Simple identity

```
if 'x' == 'x':
    'x'
else:
    'y'
```

**Fixed point:** `'x'`

## Simple liar

```
if ('x' & 'y') == 'x':
    'y'
else:
    'x'
```

**Fixed point:** `('x' & 'y')`

The comparison produces `('x': true, 'y': false)`, which selects 'y' for the 'x' case and 'x' for the 'y' case, yielding `('x': 'y', 'y': 'x')`. After normalization, this becomes `('x': 'x', 'y': 'y')`, our original value.

## Captured liar

```
if ('y' & ('x' & 'y')) == ('x' & 'y'):
    'y'
else:
    'x'
```

**Fixed point:** `('y' & ('x' & 'y'))`

The nested structure (rank 2) is compared with a rank 1 value through lifting, and after evaluation and normalization, returns to the original value.

## Escaped liar

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

## Liar's twin

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
