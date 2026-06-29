include "orders.dfy"

// Deterministic folds over sets and multisets, built on the order hierarchy. By
// refining TotalOrder, a Folds module inherits the comparison Leq and the order
// laws (Refl/Trans/Total), so the fold peels off the unique Leq-minimum each step
// WITHOUT taking a `TotalOrdering(R)` relation parameter on every operation -- the
// order is fixed once, by the module.
abstract module Folds refines TotalOrder {

    // Antisymmetry as a single quantified fact about Leq. The let-such-that picks
    // below need this in scope (phrased on Leq, not the AsRelation() lambda) to
    // know the Leq-minimum is unique, hence the pick deterministic and compilable.
    lemma LeqAntisymAll()
        ensures forall a, b :: Leq(a, b) && Leq(b, a) ==> a == b
    {
        forall a, b | Leq(a, b) && Leq(b, a) ensures a == b { Antisym(a, b); }
    }

    // Exhibit an explicit minimum witness. Keeping the existential introduction
    // in a helper with no other hypotheses keeps trigger matching cheap -- doing
    // it inline (especially for multisets) makes the prover thrash.
    lemma MinWitnessSet(s: set<T>, w: T)
        requires w in s
        requires forall y :: y in s ==> Leq(w, y)
        ensures exists m :: m in s && forall y :: y in s ==> Leq(m, y)
    {}

    lemma MinWitnessMultiset(s: multiset<T>, w: T)
        requires w in s
        requires forall y :: y in s ==> Leq(w, y)
        ensures exists m :: m in s && forall y :: y in s ==> Leq(m, y)
    {}

    // A non-empty set has a Leq-minimum element. Where the old version leaned on
    // Std.Relations' Reflexive/StronglyConnected/Transitive, this uses exactly the
    // inherited order laws: Refl, Total (connectedness), and Trans.
    lemma ThereIsAMinimum(s: set<T>)
        requires s != {}
        ensures exists m :: m in s && forall y :: y in s ==> Leq(m, y)
        decreases s
    {
        var x :| x in s;
        if s == {x} {
            assert forall y :: y in s ==> Leq(x, y) by {
                forall y | y in s ensures Leq(x, y) { Refl(x); }   // y == x
            }
            MinWitnessSet(s, x);
        } else {
            var s' := s - {x};
            ThereIsAMinimum(s');
            var y :| y in s' && forall z :: z in s' ==> Leq(y, z);
            Total(y, x);
            if Leq(y, x) {
                assert forall z :: z in s ==> Leq(y, z) by {
                    forall z | z in s ensures Leq(y, z) { if z != x { assert z in s'; } }
                }
                MinWitnessSet(s, y);
            } else {
                assert Leq(x, y);   // Total: !Leq(y,x) ==> Leq(x,y)
                assert forall z :: z in s ==> Leq(x, z) by {
                    forall z | z in s ensures Leq(x, z) {
                        if z == x { Refl(x); }
                        else { assert z in s'; Trans(x, y, z); }   // Leq(x,y) && Leq(y,z)
                    }
                }
                MinWitnessSet(s, x);
            }
        }
    }

    // Same, for multisets.
    lemma ThereIsAMinimumMultiset(s: multiset<T>)
        requires s != multiset{}
        ensures exists m :: m in s && forall y :: y in s ==> Leq(m, y)
        decreases |s|
    {
        var x :| x in s;
        var s' := s[x := 0];
        if s' == multiset{} {
            assert forall y :: y in s ==> Leq(x, y) by {
                forall y | y in s ensures Leq(x, y) {
                    if y != x { assert y in s'; }   // s' empty, contradiction
                    else { Refl(x); }
                }
            }
            MinWitnessMultiset(s, x);
        } else {
            assert |s'| < |s|;
            ThereIsAMinimumMultiset(s');
            var y :| y in s' && forall z :: z in s' ==> Leq(y, z);
            assert y in s;
            Total(y, x);
            if Leq(y, x) {
                assert forall z :: z in s ==> Leq(y, z) by {
                    forall z | z in s ensures Leq(y, z) { if z != x { assert z in s'; } }
                }
                MinWitnessMultiset(s, y);
            } else {
                assert Leq(x, y);   // Total: !Leq(y,x) ==> Leq(x,y)
                assert forall z :: z in s ==> Leq(x, z) by {
                    forall z | z in s ensures Leq(x, z) {
                        if z == x { Refl(x); }
                        else { assert z in s'; Trans(x, y, z); }
                    }
                }
                MinWitnessMultiset(s, x);
            }
        }
    }

    // Deterministic fold over a set: peels off the Leq-minimum element each step,
    // which is unique under the total order, so the result is well defined.
    function SetFold<U>(xs: set<T>, f: (T, U) -> U, init: U): U
    {
        if xs == {} then init
        else
            ThereIsAMinimum(xs);
            LeqAntisymAll();   // the Leq-minimum is unique, so the pick is deterministic
            var x :| x in xs && forall z :: z in xs ==> Leq(x, z);
            SetFold(xs - {x}, f, f(x, init))
    }

    function MultisetFold<U>(xs: multiset<T>, f: (T, U) -> U, init: U): U
        decreases |xs|
    {
        if xs == multiset{} then init
        else
            ThereIsAMinimumMultiset(xs);
            LeqAntisymAll();   // the Leq-minimum is unique, so the pick is deterministic
            var x :| x in xs && forall z :: z in xs ==> Leq(x, z);
            assert |xs[x := 0]| < |xs|;
            MultisetFold(xs[x := 0], f, f(x, init))
    }
}

// The naturals under <= : a concrete fold module. Summation is defined HERE,
// where the carrier is numeric, on top of the inherited deterministic min-fold.
module NatFold refines Folds {
    type T = nat
    predicate Leq(a: T, b: T) { a <= b }

    lemma Refl(a: T) {}
    lemma Trans(a: T, b: T, c: T) {}
    lemma Antisym(a: T, b: T) {}
    lemma Total(a: T, b: T) {}

    // Sum of a set of naturals. Peels off the Leq-minimum element so the pick is
    // unique (hence compilable); SumSetRemove shows the value is independent of
    // which element is removed (so the order only fixes the recursion, not the
    // result).
    function SumSet(s: set<nat>): nat
    {
        if s == {} then 0
        else
            ThereIsAMinimum(s);
            var m :| m in s && forall z :: z in s ==> Leq(m, z);
            m + SumSet(s - {m})
    }

    lemma SumSetRemove(s: set<nat>, y: nat)
        requires y in s
        ensures SumSet(s) == y + SumSet(s - {y})
        decreases s
    {
        ThereIsAMinimum(s);
        var m :| m in s && forall z :: z in s ==> Leq(m, z);
        assert SumSet(s) == m + SumSet(s - {m});   // matches SumSet's own pick
        if y != m {
            SumSetRemove(s - {m}, y);   // SumSet(s-{m}) == y + SumSet(s-{m}-{y})
            SumSetRemove(s - {y}, m);   // SumSet(s-{y}) == m + SumSet(s-{y}-{m})
            assert s - {m} - {y} == s - {y} - {m};
        }
    }

    lemma SumSetInsert(s: set<nat>, x: nat)
        requires x !in s
        ensures SumSet(s + {x}) == SumSet(s) + x
    {
        SumSetRemove(s + {x}, x);
        assert (s + {x}) - {x} == s;
    }
}
