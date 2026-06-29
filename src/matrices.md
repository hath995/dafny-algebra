# matrices.dfy — matrix arithmetic (abstract, law-free element ops)

Imperative matrix arithmetic over `array2<T>`, where the element type `T` and its
`Zero`/`One`/`Add`/`Mul` are abstract but carry **no algebraic laws**. This makes
it the lightweight option: a refinement only supplies the four operations. The
catch — `Add`/`Mul` must be **total**, so `nat`/`int`/`real` fit but bounded
newtypes (whose `+`/`*` overflow) do not.

Compare with [matrices_over_ring.md](matrices_over_ring.md) and
[matrices_over_semiring.md](matrices_over_semiring.md), where the element type
carries laws so matrix-level *algebraic* identities become provable.

## `Matrices`

Operations, each with a functional spec and verified loop invariants:

- `Dot` — dot product (with a `by method` for an efficient compiled version)
- `matrixAdd`, `matrixMul`, `transpose`, `scalarMul`, `hadamard`
- `trace` (with `DiagSum` spec), `identity`
- `pow` — matrix power, proved equal to the functional `MatPowEntry` via
  `PowDot` / `DotEqPowDot`

## `RingMatrices` (refines `Matrices`)

Adds `Neg` and subtraction (`Sub`, `matrixSub`) — needs an additive inverse, so
`nat` cannot refine this, only types with negation.

## Provided instances

- `NatMatrices1 : Matrices` — `T = nat`
- `IntMatrices`, `RealMatrices : RingMatrices` — `T = int` / `real` (with subtraction)

`TestMatrices.Main` squares `[[0,1],[1,2]]` and takes the trace.

## How to use

**Get matrix arithmetic for a total numeric type** with four one-liners:
```dafny
include "matrices.dfy"
module MyMats refines RingMatrices {
  type T = int
  function Zero(): T { 0 }  function One(): T { 1 }
  function Add(a: T, b: T): T { a + b }
  function Mul(a: T, b: T): T { a * b }
  function Neg(a: T): T { -a }
}
// MyMats.matrixMul(a, b), MyMats.pow(a, 3), MyMats.trace(a), MyMats.matrixSub(a, b)
```

**Choose this module** when you want runnable matrix routines and don't need to
*prove* algebraic laws about them (associativity/distributivity of the matrix
product). If you do need those, use the ring/semiring matrix modules, which take a
law-carrying element type. Build/run the demo with `dafny test src/matrices.dfy`
(it has a `Main`; or wrap your own `@Test`).
