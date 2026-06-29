# dafny-algebra — documentation

Verified abstract algebra for Dafny: an algebraic hierarchy (magma … field),
semirings, lattices/Boolean algebras, an order hierarchy with a verified merge
sort, abstract collections, subgroups, ideals, modules/vector spaces, and
matrices over rings and semirings.

Everything verifies with **no standard-library dependency** (`standard-libraries = false`).

## How the pieces fit

```
algebra.dfy ── Magma → Semigroup → Monoid → Group → AbelianGroup
                                              └→ Ring → CommRing → IntegralDomain → Field
   │
   ├── semirings.dfy        Monoid → Semiring → StarSemiring
   ├── subgroups.dfy        Subgroups[Group, Collection], GroupHom[Group, Group]
   ├── ideals.dfy           Ideals[CommRing, Collection], ZMod6Ring
   ├── modules.dfy          LeftModule[AbelianGroup, Ring], VectorSpace[AbelianGroup, Field]
   ├── matrices_over_ring.dfy        MatricesOverRing[CommRing]
   └── matrices_over_semiring.dfy    MatricesOverSemiring[Semiring]  (Floyd–Warshall)

lattices.dfy ── Lattice → DistributiveLattice → BooleanAlgebra ; Semilattice
orders.dfy   ── Preorder → PartialOrder → TotalOrder (+ merge sort) ; BoundedLattice
   ├── fold.dfy             Folds → NatFold (deterministic min-fold, SumSet)
   └── median.dfy           Medians → IntMedian/BvMedian/RealMedian

collections.dfy ── Collection → SetColl, ISetColl   (used by subgroups & ideals)
matrices.dfy    ── Matrices → RingMatrices            (element ops abstract, law-free)
```

## Per-module docs

| Doc | Source | What it gives you |
|-----|--------|-------------------|
| [algebra.md](algebra.md) | `src/algebra.dfy` | the core algebraic hierarchy, `IntRing`, `RealField` |
| [semirings.md](semirings.md) | `src/semirings.dfy` | semirings, star semirings, the tropical (min,+) dioid |
| [lattices.md](lattices.md) | `src/lattices.dfy` | lattices, distributive lattices, Boolean algebras, semilattices |
| [orders.md](orders.md) | `src/orders.dfy` | preorder/partial/total order, a verified merge sort, bounded lattices |
| [collections.md](collections.md) | `src/collections.dfy` | an abstract set type (set vs iset) with a proved set algebra |
| [subgroups.md](subgroups.md) | `src/subgroups.dfy` | subgroup theory + group homomorphisms, parameterized |
| [ideals.md](ideals.md) | `src/ideals.dfy` | ring ideals + the quotient `Z/6Z` |
| [modules.md](modules.md) | `src/modules.dfy` | modules over a ring and vector spaces over a field |
| [fold.md](fold.md) | `src/fold.dfy` | deterministic order-driven folds; `SumSet` |
| [median.md](median.md) | `src/median.dfy` | order-statistic medians on top of the sort |
| [matrices.md](matrices.md) | `src/matrices.dfy` | matrix arithmetic with abstract, law-free element ops |
| [matrices_over_ring.md](matrices_over_ring.md) | `src/matrices_over_ring.dfy` | matrices over a `CommRing` (laws provable) |
| [matrices_over_semiring.md](matrices_over_semiring.md) | `src/matrices_over_semiring.dfy` | matrices over a `Semiring`; tropical = shortest paths |
| [examples.md](examples.md) | `examples/` | two structures over one object: ordered group, tree monoid |

## Two ways to use a module

1. **Use a provided concrete instance** — import it and call its functions/lemmas:
   ```dafny
   include "src/algebra.dfy"
   module UseInts { import R = IntRing
     lemma demo() { R.MulComm(2, 3); }   // 2*3 == 3*2, from the proved law
   }
   ```
2. **Make your own instance** by refining an abstract module: supply the carrier
   `type T`, the operation functions, and discharge the law lemmas (usually `{}`
   when the carrier is `int`/`real`/`bool` and the verifier proves them for free):
   ```dafny
   module MyMonoid refines Monoid {
     type T = string
     function op(a: T, b: T): T { a + b }
     function Id(): T { "" }
     lemma Assoc(a: T, b: T, c: T) {}
     lemma LeftId(a: T) {}
     lemma RightId(a: T) {}
   }
   ```
   Import-parameterized modules (Collections, Subgroups, Ideals, Modules, the
   matrix-over-ring/semiring modules) are instantiated by binding their imports:
   `module M refines Ideals { import R = IntRing; import L = ISetColl }`.

## Verifying and running

```sh
dafny verify src/<file>.dfy           # verify one file (includes pull in deps)
dafny test  examples/<file>.dfy       # run an @Test demo (e.g. median, tree_monoid)
```

There is no `--standard-libraries` flag needed; the project config sets it off.
Executable demos are `@Test`-attributed methods — run them with `dafny test`.
