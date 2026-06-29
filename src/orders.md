# orders.dfy — the order hierarchy and a verified merge sort

The order-theoretic companion to the algebraic chain, plus a sort that every total
order gets for free.

```
Preorder → PartialOrder → TotalOrder        BoundedLattice (refines Lattice)
```

`Leq` is a **compiled** predicate (not ghost) so it can drive executable code.

## `Preorder` / `PartialOrder` / `TotalOrder`

| Module | Adds | Derived |
|--------|------|---------|
| `Preorder` | `Leq`, `Refl`, `Trans` | `Lt` (strict part), `LtIrrefl` |
| `PartialOrder` | `Antisym` | `LtTrans`, `LtAsym` |
| `TotalOrder` | `Total` | `Trichotomy`, **the merge sort below** |

## The merge sort (in `TotalOrder`)

Because sorting needs exactly a total order, it lives here and every `TotalOrder`
(hence `IntOrder`, `Folds`, `Medians`) inherits it. Written directly against `Leq`
— no relation parameter, no standard library:

- `ghost predicate SortedBy(s)` — pairwise sorted
- `function Sorted(xs)` — merge sort; ensures `multiset` preserved, `|·|` preserved, `SortedBy`
- `function MergeWith(left, right)` — merge two sorted sequences
- supporting lemmas `HeadIsLeast`, `TailBounded`, `PrependBelow`, `MergeBelow`
- **`SortedUnique`** — a total order admits a *unique* sorted arrangement of any
  multiset (two sorted sequences with the same elements are identical)

## `BoundedLattice`

Refines `Lattice` (from `lattices.dfy`) with `Top`/`Bot` identity laws and proves
`BotLeast` (`Bot ≤ a`) and `TopGreatest` (`a ≤ Top`).

## Provided instances

- `IntOrder : TotalOrder` — `(ℤ, ≤)`; gives you `IntOrder.Sorted`, `MergeWith`, …
- `BoolSetLattice : BoundedLattice` — `set<bool>` under `∪`/`∩`, `Top = {false,true}`.

## How to use

**Sort by your own order** — refine `TotalOrder`, supply `Leq` and the four laws,
and you get a verified `Sorted`:
```dafny
include "orders.dfy"
module ByAbs refines TotalOrder {
  type T = int
  predicate Leq(a: T, b: T) { (if a < 0 then -a else a) <= (if b < 0 then -b else b) }
  lemma Refl(a: T) {}  lemma Trans(a: T, b: T, c: T) {}
  lemma Antisym(a: T, b: T) {}  lemma Total(a: T, b: T) {}
}
// ByAbs.Sorted([-3, 1, 2]) is provably SortedBy(ByAbs.Leq) and a permutation.
```
(Antisymmetry must genuinely hold — `ByAbs` above orders `-3` and `3` as equal, so
tweak `Leq` or accept that `Antisym` will fail to verify.)

**Reuse `Sorted`/`SortedUnique`** when you need "the" sorted form of data — see
`fold.dfy` (deterministic min-fold), `median.dfy` (order statistics), and
`examples/tree_monoid.dfy` (sorting the leaves of a composed tree, where
`SortedUnique` proves *sort(s·t) = merge(sort s, sort t)*).

**Use `Preorder`/`PartialOrder`** directly when you only need the relational laws
(not a sort) — e.g. to state monotonicity hypotheses generically.
