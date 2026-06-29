# ideals.dfy — ring ideals and a quotient ring

The ring analogue of `subgroups.dfy`: an ideal is exactly what you can quotient a
ring by. Parameterized by both the ring and the collection carrier.

## `Ideals`

```dafny
abstract module Ideals { import R : CommRing; import L : Collection }
```

`IsIdeal(s)` = an additive subgroup of `(R, +)` that also **absorbs**
multiplication by any ring element (`r·a ∈ s`). Proved generically:

- `ZeroIdeal` — `{0}` is an ideal (absorption from `r·0 = 0`)
- `IdealIntersect` — the intersection of two ideals is an ideal
- `IdealClosedUnderPow` — closed under natural multiples

## Provided instances

- `IntIdeals` (`R = IntRing`, `L = ISetColl`) — proves the principal ideal
  `(n) = nℤ` is an ideal (`MultiplesIdeal`), and the evens `2ℤ` (`EvensIdeal`).
  Every ideal of ℤ is principal, so these are *all* of them.
- `ZMod6Ring : CommRing` — the **quotient** `Z/6Z = Z / (6Z)`. Its mod-6 ring laws
  are proved from self-contained modular-arithmetic lemmas (`AddMultiple`,
  `ModMulLeft/Right`, `AddModBoth` — no standard library). `HasZeroDivisors`
  exhibits `2·3 ≡ 0`: quotienting by a **non-prime** loses the integral-domain
  property (contrast `IntRing`, an integral domain — see [algebra.md](algebra.md)).

## How to use

**Instantiate ideal theory** for a commutative ring:
```dafny
include "ideals.dfy"
module MyIdeals refines Ideals {
  import R = IntRing
  import L = ISetColl
  lemma threeZ() { MultiplesIdeal(3); }   // 3ℤ is an ideal of ℤ
}
```

**As a teaching pair with `algebra.dfy`:** `IntRing` is an integral domain;
`ZMod6Ring` is the quotient by `6ℤ` and is *not* (it has zero divisors). Use
`ZMod6Ring` as a template for any `Z/nZ` ring — the modular-arithmetic helper
lemmas generalize by swapping the modulus.

Pick `ISetColl` (infinite carrier) for ideals like `nℤ`; `SetColl` if you are
working inside a finite ring.
