# matrices_over_ring.dfy — matrices over a commutative ring

Matrices whose **element type is an arbitrary commutative ring**, supplied as a
module parameter (`import R : CommRing`). Unlike [matrices.md](matrices.md), where
the element ops are law-free, here `R` carries `Assoc`/`Comm`/`Distrib`, so
matrix-level algebraic laws become **provable** rather than merely assumed.

Naming (from the algebra hierarchy): `R.op` is addition, `R.Id()` the additive
zero, `R.mul` multiplication, `R.One()` the one.

## `MatricesOverRing`

```dafny
abstract module MatricesOverRing { import R : CommRing }
```

- `Dot`, `matrixAdd`, `matrixMul` — the arithmetic
- `AddRearrange4` — `(w+x)+(y+z) = (w+y)+(x+z)` from add assoc/comm
- `DotDistrib` — the dot product distributes over an element-wise sum
- `MatMulDistrib` — entry-wise matrix distributivity
  `(A·(B+C))[i,j] = (A·B)[i,j] + (A·C)[i,j]`, proved from the **element ring laws**

(The comment in the source notes that matrix-mul associativity and the identity
law are the natural next theorems; the semiring version proves associativity in
full — see below.)

## Provided instance

- `IntMatricesOverRing` — `R = IntRing`.

## How to use

**Get law-backed matrix algebra over any commutative ring** by binding `R`:
```dafny
include "matrices_over_ring.dfy"
module RealMats refines MatricesOverRing { import R = RealField }   // Field ⊂ CommRing
// RealMats.matrixMul(a, b); RealMats.MatMulDistrib(a, b, c, bc);  -- distributivity is a theorem
```

**Pick this over `matrices.dfy`** when you need to *reason* about the matrix
operations (distributivity, and as a basis for further identities), not just run
them. The element ring can be any `CommRing` — `IntRing`, `RealField`, or a
`ZMod` ring from [ideals.md](ideals.md). If your element type is an *additive
monoid without inverses* (min-plus, booleans, counts), use the **semiring** version
in [matrices_over_semiring.md](matrices_over_semiring.md) instead.
