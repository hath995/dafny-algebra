# subgroups.dfy — subgroup theory and homomorphisms

Subgroup theory written **once** and reused for finite and infinite groups, plus
group homomorphisms. Both are parameterized by imports (the established Dafny idiom
for combining structures over related carriers).

## `Subgroups`

```dafny
abstract module Subgroups { import G : Group; import L : Collection }
```

`IsSubgroup(s)` = contains the identity, closed under `op`, closed under `Inv`.
Proved generically (for any group `G`, any carrier `L`):

- `TrivialSubgroup` — `{e}` is a subgroup
- `SubgroupIntersect` — the intersection of two subgroups is a subgroup
- `SubgroupClosedUnderPow` — a subgroup is closed under natural powers

## `GroupHom`

```dafny
abstract module GroupHom { import G : Group; import H : Group; function F(a: G.T): H.T }
```

A single law `HomLaw` (`F` preserves `op`) **forces** `F` to preserve identity and
inverses — proved once for every instantiation: `FId` (`F(e_G) = e_H`) and `FInv`
(`F(a⁻¹) = F(a)⁻¹`). Also defines `Injective`.

## Provided instances

- `IntSetSubgroups` / `IntISetSubgroups` — subgroups of `(ℤ, +)`, finite and
  infinite; the latter proves `nℤ` and the evens are subgroups, and all of ℤ is.
- `KleinFour : AbelianGroup` and `KleinSubgroups` — the Klein four-group `(Z/2)²`
  and its three order-2 subgroups + the whole group.
- `ZMod12`, `ZMod4 : AbelianGroup`; `ZMod12Subgroups` — the cyclic subgroups
  `{0,3,6,9}≅Z/4`, `{0,4,8}≅Z/3`, `{0,6}≅Z/2`.
- `Z4toZ12 : GroupHom` — the embedding `Z/4 ↪ Z/12`, `k ↦ 3k mod 12`, shown
  injective with image exactly `{0,3,6,9}`.

## How to use

**Instantiate the theory** for your group by binding both imports:
```dafny
include "subgroups.dfy"
module MySubs refines Subgroups {
  import G = KleinFour     // any module that refines Group
  import L = SetColl       // finite carrier; use ISetColl for infinite groups
  lemma exampleSub() { TrivialSubgroup(); }   // {e} ⊆ KleinFour, for free
}
```
Pick `SetColl` for finite groups, `ISetColl` for infinite ones (e.g. `nℤ`) — the
subgroup proofs are identical either way.

**Define a homomorphism** by refining `GroupHom`, binding `G`/`H`, supplying `F`,
and discharging `HomLaw`; you then get identity/inverse preservation for free.
This is the model for "a lemma needing laws from two structures" — `FId`/`FInv`
use cancellation in `H` and the operation law in `G`.
