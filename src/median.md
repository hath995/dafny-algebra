# median.dfy — order-statistic medians

Medians built on the order hierarchy: a `Medians` module *is* a `TotalOrder` (it
refines it), inheriting `Leq`, the four order laws, **and** the verified merge sort
(`Sorted`/`SortedBy`) from `orders.dfy`. All that is added here is averaging and
the median itself — no order hypothesis on any operation, no standard library.

## `Medians` (refines `TotalOrder`)

- `add`, `halve` — abstract averaging primitives (supplied per instance)
- `Median(xs)` — sorts `xs`; returns the middle element (odd length) or the
  average of the two central order statistics (even length)
- proved properties:
  - `MedianSplitsOdd` — the median is the middle of the sorted data; lower half
    `≤` it, upper half `≥` it
  - `MedianBalanceOdd` — the rank/balance view on the *original* data: at least
    half is `≤` the median and at least half is `≥` it
  - `MedianSplitsEven` — for even length, given that averaging stays between its
    inputs (a hypothesis, discharged by the concrete instances)

## Provided instances

| Instance | `T` | `halve(add(a,b))` | even-length median valid? |
|----------|-----|-------------------|---------------------------|
| `IntMedian` | `int` | `(a+b)/2` (floor) | yes (`Averaging`) |
| `RealMedian` | `real` | `(a+b)/2.0` | yes (exact) |
| `BvMedian` | `bv8` | `(a+b) >> 1` | no — averaging can overflow |

`BvMedian` deliberately omits the averaging lemma, illustrating that the
even-length guarantee is exactly the "averaging stays between its inputs" property.

## How to use

**Medians over your own ordered type** — refine `Medians`, supply `Leq` + the four
order laws + `add`/`halve`:
```dafny
include "median.dfy"
module IntMedian refines Medians {
  type T = int
  function add(a: T, b: T): T { a + b }
  function halve(a: T): T { a / 2 }
  predicate Leq(a: T, b: T) { a <= b }
  lemma Refl(a: T) {} lemma Trans(a: T, b: T, c: T) {}
  lemma Antisym(a: T, b: T) {} lemma Total(a: T, b: T) {}
  lemma Averaging()   // optional: validates the even-length median
    ensures forall a, b :: Leq(a, b) ==> Leq(a, halve(add(a, b))) && Leq(halve(add(a, b)), b) {}
}
```

Run the demo with `dafny test src/median.dfy` (an `@Test` method prints the median
of `[1,2,3,4,5]` for ints and `bv8`). This module is also the canonical example of
*consuming* the `TotalOrder` merge sort from [orders.md](orders.md).
