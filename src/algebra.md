# algebra.dfy — the algebraic hierarchy

A linear refinement chain along a single operation, each step adding one law:

```
Magma → Semigroup → Monoid → Group → AbelianGroup → Ring → CommRing → IntegralDomain → Field
```

Dafny modules support **single** refinement, so the chain is linear. `Ring` is
where that bites: a ring is an additive abelian group *and* a multiplicative
monoid, so `Ring` refines the additive `AbelianGroup` and **inlines** the
multiplicative structure (`mul`, `One`, its associativity/identity, distributivity).

## Modules and their laws

| Module | Adds | Key derived lemmas (proved once, inherited) |
|--------|------|---------------------------------------------|
| `Magma` | `type T`, `op` | — |
| `Semigroup` | `Assoc` | `Assoc4` (any bracketing of 4 is equal) |
| `Monoid` | `Id`, `LeftId`, `RightId` | `IdentityUnique`, `pow`, `Pow1`, `PowAdd`, `PowMul`, `PowLeft` |
| `Group` | `Inv`, `LeftInv`, `RightInv` | `LeftCancel`, `RightCancel`, `InvUnique(Right)`, `InvInv`, `InvId`, `InvOp`, `PowInv`, `PowSubtract` |
| `AbelianGroup` | `Comm` | `InvOpAbelian` |
| `Ring` | `mul`, `One`, `MulAssoc`, `Mul(Left/Right)Id`, `(Left/Right)Distrib` | `MulZeroLeft/Right`, `MulNegLeft/Right` |
| `CommRing` | `MulComm` | — |
| `IntegralDomain` | `NoZeroDivisors` (axiom) | `MulCancel` (cancel a nonzero factor) |
| `Field` | `MulInv`, `MulLeftInv` | `MulRightInv`, `NoZeroDivisors` (here *proved*, discharging the axiom) |

`IntegralDomain` is the rung that lets the integers be classified exactly: `IntRing`
is an integral domain but not a field. Every `Field` is an integral domain (the
`NoZeroDivisors` axiom is discharged from `MulInv`).

## Provided instances

- `IntRing : IntegralDomain` — `(ℤ, +, 0, −, ·, 1)`.
- `RealField : Field` — `(ℝ, +, 0, −, ·, 1, ⁻¹)`.

## How to use

**Reuse the proved laws of an instance:**
```dafny
include "algebra.dfy"
module Demo { import R = IntRing
  lemma cancel(a: int, b: int, c: int)
    requires a != 0 && a * b == a * c
    ensures b == c
  { R.MulCancel(a, b, c); }   // integral-domain cancellation, proved generically
}
```

**Define a new structure** by refining the right rung and discharging its laws.
A finite group, for instance (see also `KleinFour`, `ZMod12` in `subgroups.dfy`):
```dafny
module Z2 refines AbelianGroup {
  type T = bool                       // {false, true} ≅ Z/2Z under XOR
  function op(a: T, b: T): T { a != b }
  function Id(): T { false }
  function Inv(a: T): T { a }          // self-inverse
  lemma Assoc(a: T, b: T, c: T) {}
  lemma LeftId(a: T) {} lemma RightId(a: T) {}
  lemma LeftInv(a: T) {} lemma RightInv(a: T) {}
  lemma Comm(a: T, b: T) {}
}
```
Once refined you immediately get `pow`, cancellation, `InvInv`, `InvOp`, etc. for free.

**When to pick which rung:** need an identity → `Monoid`; inverses → `Group`;
commutativity → `AbelianGroup`; a second (multiplicative) operation with
distributivity → `Ring`/`CommRing`; division → `Field`. If you only need "no zero
divisors / cancellation" but not division, stop at `IntegralDomain`.

**Downstream:** `semirings.dfy` (drop additive inverses), `subgroups.dfy`,
`ideals.dfy`, `modules.dfy`, and `matrices_over_ring.dfy` all build on this file.
