# fold.dfy — deterministic, order-driven folds

Folds over sets and multisets that are **deterministic** because they peel off the
unique `Leq`-minimum each step. Built on the order hierarchy: a `Folds` module *is*
a `TotalOrder` (it refines it), so it inherits `Leq` and the order laws and needs
no `TotalOrdering(R)` relation parameter.

## `Folds` (refines `TotalOrder`)

- `ThereIsAMinimum` / `ThereIsAMinimumMultiset` — a non-empty set/multiset has a
  `Leq`-minimum (proved from `Refl`, `Total`, `Trans` — no standard library)
- `MinWitnessSet` / `MinWitnessMultiset` — cheap existential-introduction helpers
- `SetFold<U>` / `MultisetFold<U>` — fold by repeatedly removing the minimum; the
  pick is unique under the total order (`LeqAntisymAll`), so the result is well-defined

## `NatFold` (refines `Folds`, `T = nat`)

Summation lives here, where the carrier is numeric, on top of the inherited
min-fold:

- `SumSet(s)` — sum of a set of naturals
- `SumSetRemove`, `SumSetInsert` — the value is independent of which element is
  peeled (so the order fixes only the recursion, not the result)

## How to use

**Fold over your own ordered carrier** — refine `Folds`, supply `Leq` + the four
order laws, and you get `SetFold`/`MultisetFold`:
```dafny
include "fold.dfy"
module IntFold refines Folds {
  type T = int
  predicate Leq(a: T, b: T) { a <= b }
  lemma Refl(a: T) {} lemma Trans(a: T, b: T, c: T) {}
  lemma Antisym(a: T, b: T) {} lemma Total(a: T, b: T) {}
}
// IntFold.SetFold({3,1,2}, (x, acc) => acc + [x], [])  ==  [1,2,3] (ascending)
```

The key property: because elements are consumed in `Leq` order and the minimum is
unique, `SetFold` is a genuine **function** (deterministic), not just a relation —
useful when you need a canonical reduction of an unordered collection (sums,
products, building a sorted list, hashing a set reproducibly). For numeric sums
specifically, reuse `NatFold.SumSet` directly.
