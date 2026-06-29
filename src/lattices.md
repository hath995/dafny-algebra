# lattices.dfy — lattices, Boolean algebras, semilattices

The bridge between the **algebraic** and **order-theoretic** views of a lattice:
from the lattice axioms alone, the relation `a ≤ b :⟺ a ∧ b = a` is proved to be a
partial order.

```
Lattice → DistributiveLattice → BooleanAlgebra
Semilattice            (the single-operation fragment)
```

## `Lattice`

Two commutative, associative, idempotent operations `join` (∨) and `meet` (∧)
linked by the two **absorption** laws. Derived:

- `Consistency` — `a ∧ b = a ⟺ a ∨ b = b` (the two ways to say `a ≤ b` agree)
- `LeqRefl`, `LeqAntisym`, `LeqTrans` — the induced `Leq` is a partial order

## `DistributiveLattice`

Adds both distributive laws and proves **`Cancellation`**: in a distributive
lattice an element is pinned down by its meet and join with any fixed element
(false in a general lattice).

## `BooleanAlgebra`

Adds `Top`, `Bot`, `Compl` with the bound/complement laws. Derived (using
`Cancellation`): **complement uniqueness** (`ComplUnique`), **double complement**
(`ComplCompl`), and both **De Morgan** laws (`DeMorganJoin`, `DeMorganMeet`), plus
`MeetBot`/`JoinTop` annihilation.

## `Semilattice`

One commutative/associative/**idempotent** operation `op`. It induces the same
order `a ≤ b :⟺ op(a,b) = a` as a lattice, and `op` is proved to be the **greatest
lower bound** (`OpLowerLeft/Right`, `OpGreatest`). A lattice is two semilattices
(join and meet) glued by absorption.

## Provided instances

| Instance | Carrier | join / meet | Notes |
|----------|---------|-------------|-------|
| `SetLattice` | `set<int>` | `∪` / `∩` | the canonical distributive lattice |
| `MinMaxLattice` | `int` | `max` / `min` | a chain; `Leq` is the usual `≤` |
| `BoolAlgebra` | `bool` | `‖` / `&&`, `!` | the two-element Boolean algebra |
| `PowersetAlgebra` | `set<bool>` | `∪` / `∩`, complement vs `{false,true}` | the 4-element powerset |
| `MinSemilattice` | `int` | `min` | prototypical meet-semilattice |

## How to use

**Get a partial order for free** from any lattice you define — refine `Lattice`,
supply `join`/`meet`, discharge the eight axioms, and you inherit `Leq` plus
reflexivity/antisymmetry/transitivity:
```dafny
include "lattices.dfy"
module DivLattice refines DistributiveLattice {
  // join = lcm, meet = gcd over positive nats, say — discharge comm/assoc/idem/absorb/distrib
}
```

**Reach for `BooleanAlgebra`** when you have complements (sets-with-universe, bit
masks, propositions) and want De Morgan / double-negation as proved facts. Reach
for `Semilattice` when you have only one idempotent combiner (min, max, ∪, gcd)
and want its "greatest lower bound" characterization.

See also `BoundedLattice` in [orders.md](orders.md) (a lattice with `Top`/`Bot`
where `Bot ≤ x ≤ Top` is proved).
