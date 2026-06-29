# semirings.dfy — semirings and star semirings

A **semiring** is like a ring but **without additive inverses**: an additive
commutative monoid plus a multiplicative monoid, linked by distributivity. The one
structural difference from `Ring`: because there is no additive inverse to cancel
with, `0·a = 0` (annihilation) must be taken as an **axiom** here rather than derived.

```
Monoid (from algebra.dfy) → Semiring → StarSemiring
```

## `Semiring`

Refines the additive `Monoid` (so `op = +`, `Id() = 0`, and `pow` are inherited),
declares `Comm` for addition, and inlines a multiplicative monoid:

- `mul`, `One`, `MulAssoc`, `MulLeftId`, `MulRightId`
- `LeftDistrib`, `RightDistrib` (both kept — multiplication need not commute)
- `MulZeroLeft`, `MulZeroRight` (annihilation **axioms**)
- derived: `MulDistribBoth` (the FOIL expansion)

## `StarSemiring`

Adds a unary `star` with the two fixpoint-unfolding laws
`a* = 1 + a·a* = 1 + a*·a` — the reflexive-transitive-closure operator behind
Kleene's theorem and transitive closure. Derived: `StarZero` (`0* = 1`).

## Provided instances

| Instance | Carrier | `+` / `0` | `·` / `1` | Notes |
|----------|---------|-----------|-----------|-------|
| `NatSemiring` | `nat` | `+` / `0` | `·` / `1` | the prototype (no negatives) |
| `BoolSemiring` | `bool` | `‖` / `false` | `&&` / `true` | idempotent |
| `Tropical` | `Inf │ Fin(int)` | `min` / `+∞` | `+` / `0` | the (min,+) **dioid**; +order lemmas |
| `BoolStarSemiring` | `bool` | `‖` / `false` | `&&` / `true` | `star(_) = true` (reachability) |

`Tropical` also proves order facts (`OpIdem`, `LeqTrans`, `MulMono`, …): its
addition (min) is idempotent, so it is a semilattice and the semiring is a dioid —
exactly what the shortest-path reading of a matrix product needs.

## How to use

**Build a semiring:** supply `op/Id/mul/One` and discharge the laws (including the
two annihilation axioms — trivial for the usual carriers):
```dafny
include "semirings.dfy"
module MaxPlus refines Semiring {       // the (max, +) "arctic" semiring sketch
  // ... op = max with identity −∞, mul = +, One = 0, etc.
}
```

**Feed it to matrices:** `matrices_over_semiring.dfy` takes `import R : Semiring`.
Instantiating with `Tropical` makes one matrix product a round of shortest-path
relaxation, and iterating it (Floyd–Warshall) computes all-pairs shortest paths —
see [matrices_over_semiring.md](matrices_over_semiring.md).

**When to use a semiring vs a ring:** choose `Semiring` when your "addition" has no
inverse (counts, booleans, min/max, languages). If you have subtraction, use
`Ring`/`CommRing` from [algebra.md](algebra.md) instead and get `0·a = 0` for free.
