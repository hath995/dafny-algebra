# matrices_over_semiring.dfy — matrices over a semiring (shortest paths)

The same matrix code as [matrices_over_ring.md](matrices_over_ring.md), but over an
arbitrary **semiring** (`import R : Semiring`) — nothing here uses an additive
inverse or multiplicative commutativity, so the dot product, add/mul, and
distributivity port verbatim. The payoff: instantiating `R = Tropical` turns matrix
multiplication into one round of **shortest-path relaxation**, and that reading is
*proved*.

## `MatricesOverSemiring`

```dafny
abstract module MatricesOverSemiring { import R : Semiring }
```

- arithmetic: `Dot`, `matrixAdd`, `matrixMul`
- distributivity: `AddRearrange4`, `DotDistrib`, `MatMulDistrib`
- **associativity of matrix multiplication**, in full: a double-sum swap
  (`Fubini`) plus the row/column inner-sum machinery
  (`RowInner`/`ColInner`/`DSumRow`/`DSumCol`, `…IsScaledDot`, `DSumColPeel`,
  `DotAbIsDSumCol`/`DotBcIsDSumRow`) culminating in `MatMulAssoc`
- a **closed-form / generic** layer over index functions `(nat,nat) -> R.T`
  (`GDot`, `GMul`, `GId`, `GPow`, `MatMulIsGMul`, …) used to talk about powers and
  walks abstractly

## `TropicalMatrices` (refines with `R = Tropical`)

The shortest-path interpretation, proved:

- `DotLowerBound` / `DotAchieved` — a matrix product entry is the min over an
  intermediate node, and that minimum is attained
- `WalkWeight`, `WalkSound`, `WalkTight` — relate matrix powers to weighted walks
- `SVBase` / `SVStep` and **`FloydWarshall`** — an imperative all-pairs
  shortest-paths method, verified against the walk semantics

## Provided instances

- `NatMatrices : MatricesOverSemiring` — `R = NatSemiring`.
- `TropicalMatrices : MatricesOverSemiring` — `R = Tropical`, with the
  shortest-path theorems above.

## How to use

**Matrix algebra over any semiring** — bind `R`:
```dafny
include "matrices_over_semiring.dfy"
module BoolMats refines MatricesOverSemiring { import R = BoolSemiring }
// boolean matrix product = reachability in one step; iterate for transitive closure
```

**Shortest paths:** use `TropicalMatrices` — `matrixMul` relaxes one hop and
`FloydWarshall` computes all-pairs shortest distances, both verified. This is the
flagship "the algebra *is* the algorithm" example: the same proved `matrixMul`
means counting walks over `NatSemiring`, reachability over `BoolSemiring`, and
shortest paths over `Tropical`. See [semirings.md](semirings.md) for the element
structures.
