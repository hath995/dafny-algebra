# modules.dfy — modules and vector spaces

An abelian group of "vectors" acted on by a ring (or field) of "scalars".
Parameterized by imports — the additive group (`V`) and the scalar ring (`R`/`F`)
— with the scalar action `smul` declared abstractly. Conceptually the parent of
the matrix modules: an m×n matrix is an element of a module over its entry ring.

## `LeftModule`

```dafny
abstract module LeftModule { import R : Ring; import V : AbelianGroup
  function smul(r: R.T, v: V.T): V.T }
```

The four module axioms (`ScalarDistribVec`, `ScalarDistribScalar`, `ScalarAssoc`,
`ScalarOne`), from which it **proves**:

- `ZeroScalar` — `0_R · v = 0_V`
- `ScalarZeroVec` — `r · 0_V = 0_V`
- `NegScalar` — `(−r) · v = −(r · v)`

## `VectorSpace`

Same, but scalars form a `Field` (written separately because Dafny's single
refinement can't strengthen the imported ring into a field). The extra structure
buys **`ScalarCancel`**: a nonzero scalar cancels (`r ≠ 0 ∧ r·u = r·v ⟹ u = v`),
proved by multiplying through by `r⁻¹`.

## Provided instances

- `IntPairGroup`, `RealPairGroup : AbelianGroup` — `ℤ²` and `ℝ²` (componentwise).
- `ZModule : LeftModule` — `ℤ²` over `IntRing`, componentwise scaling.
- `R2Space : VectorSpace` — `ℝ²` over `RealField`.

## How to use

**Define a module/space** by binding the additive group and scalar ring and giving
`smul`:
```dafny
include "modules.dfy"
module ZmodScaled refines LeftModule {
  import R = IntRing
  import V = IntPairGroup
  function smul(r: R.T, v: V.T): V.T { V.V2(r * v.x, r * v.y) }
  lemma ScalarDistribVec(r: R.T, u: V.T, w: V.T) {}
  lemma ScalarDistribScalar(r: R.T, s: R.T, v: V.T) {}
  lemma ScalarAssoc(r: R.T, s: R.T, v: V.T) {}
  lemma ScalarOne(v: V.T) {}
  // inherits ZeroScalar / ScalarZeroVec / NegScalar
}
```
Use `LeftModule` when scalars are a ring (e.g. ℤ-modules, abelian groups as
ℤ-modules); use `VectorSpace` when scalars are a field and you want nonzero-scalar
cancellation. The `V`/`R` import pattern is the same one used by `subgroups.dfy`
and `ideals.dfy`.
