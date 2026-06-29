# collections.dfy — an abstract set type

An abstract collection (set) type whose **concrete container is itself abstract**,
so a theory written once works for both finite (`set`) and infinite (`iset`)
carriers. The whole point: write set-using theories (like subgroups and ideals)
*once*, against `Collection`, and instantiate them with `SetColl` or `ISetColl`.

## `Collection`

Declares an opaque `type C<A>` with membership `In` and the operations
`Empty`, `Single`, `Union`, `Inter`, `Diff`, `Subset`, each with a
**characterization law** saying what it means member-wise (`UnionChar`,
`InterChar`, …), plus `Extensionality`.

From those laws alone it **proves the full set algebra once**: commutativity,
associativity, idempotence, identity/annihilation of `Empty`, both distributive
laws, both absorption laws, and **De Morgan** (`DeMorganUnion`, `DeMorganInter`).
Instances inherit all of it.

## Provided instances

- `SetColl` — finite sets (`C<A> = set<A>`).
- `ISetColl` — arbitrary, possibly infinite sets (`C<A> = iset<A>`).

Each just defines the operations as the built-in set ops and discharges the
characterization laws (mostly `{}`).

## How to use

This module is the **collection parameter** for `subgroups.dfy` and `ideals.dfy`.
Write a theory once over an abstract `import L : Collection`, then pick the carrier
at instantiation:
```dafny
include "collections.dfy"
abstract module MyTheory {
  import L : Collection
  ghost predicate Closed<A(==,!new)>(s: L.C<A>, f: A -> A) {
    forall x :: L.In(x, s) ==> L.In(f(x), s)
  }
}
module FiniteTheory  refines MyTheory { import L = SetColl }   // finite version
module InfiniteTheory refines MyTheory { import L = ISetColl } // infinite version, same proofs
```

Use `SetColl` when membership is decidable/finite (concrete finite subgroups,
finite ideals); use `ISetColl` for whole-space objects like `nℤ` or "all of ℤ".
Because the derived set algebra is proved abstractly, neither instance re-proves it.
