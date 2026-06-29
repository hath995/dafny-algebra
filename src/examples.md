# examples/ — one object, two structures

Two worked examples where a single object satisfies **two** of the library's
structures and a lemma genuinely needs laws from both. Both run with `dafny test`.

## `ordered_group.dfy` — an ordered abelian group

One carrier that is simultaneously:

- an **`AbelianGroup`** (`src/algebra.dfy`) — *refined*, so it inherits `op/Id/Inv`
  and all derived group lemmas (`InvId`, `InvInv`, cancellation, …);
- a **total order** (the `TotalOrder` interface of `src/orders.dfy`) — *inlined*,
  because Dafny modules have single refinement (the same trick `Ring` uses to be
  both an additive group and a multiplicative monoid).

Tied together by one **compatibility axiom**, `TransInvariant` (the order is
translation-invariant). Lemmas whose proofs interleave both structures:

- `InvReversesOrder` — `a ≤ b ⟹ −b ≤ −a` (order-compat + group axioms)
- `StrictInvReverses` — the strict version; needs the *derived* group lemma `InvInv`
- `SignDichotomy` — every element is `≥ 0` or its inverse is (order's `Total` +
  group's `InvId`)
- `OrderIffNonnegDifference`, `TransReflect` — the order is the sign of the difference

Instantiated as `IntOrderedGroup` over `(ℤ, +, 0, −, ≤)`; the abstract lemmas
specialize to concrete integer facts. **Run:** `dafny test examples/ordered_group.dfy`.

## `tree_monoid.dfy` — a tree monoid sorted by its elements

A richer carrier where the structure laws are **not** free (unlike `int`):

- `Tree<A>` is a **`Monoid`** under composition `comp` with `Nil` identity
  (`TreeMonoid refines Monoid`, `T = Tree<int>`); associativity is a real induction.
- the element type is a **`TotalOrder`** (`IntOrder`), giving a verified merge sort
  on the leaves.

Capstone, combining both (`SortLeavesOfComposition`):

```
sort(leaves(s `comp` t))  ==  merge(sort(leaves s), sort(leaves t))
```

The **Monoid** side supplies the homomorphism `leaves(s·t) = leaves(s) ++ leaves(t)`;
the **TotalOrder** side supplies `MergeWith`, `Sorted`, and `SortedUnique` (the
uniqueness of sorted arrangements). Also `SortRespectsAssociativity` (via `M.Assoc`)
and `SortIgnoresIdentity` (via `M.RightId`). **Run:** `dafny test examples/tree_monoid.dfy`.

## Takeaway: how to combine two structures over one carrier

Dafny has single-module refinement and cannot unify the abstract carrier types of
two independent imports, so:

- **Same carrier, both structures** → refine one structure, inline the other's
  operations + laws (the `ordered_group.dfy` / `Ring` pattern).
- **Related carriers** → use the import idiom: one structure on the object, another
  on a related type, combined in a third module (the `tree_monoid.dfy` /
  `subgroups.dfy` / `modules.dfy` pattern). This is preferred when the laws must
  stay abstract, because over a concrete shared type (like `int`) the verifier
  proves cross-cutting goals by computation and the structure laws go unused.
