module Fold {
    import opened Std.Relations

    // Exhibit an explicit minimum witness. Keeping the existential introduction
    // in a helper with no other hypotheses keeps trigger matching cheap — doing
    // it inline (especially for multisets) makes the prover thrash.
    lemma MinWitnessSet<T(!new)>(R: (T, T) -> bool, s: set<T>, w: T)
        requires w in s
        requires forall y :: y in s ==> R(w, y)
        ensures exists m :: m in s && forall y :: y in s ==> R(m, y)
    {}

    lemma MinWitnessMultiset<T(!new)>(R: (T, T) -> bool, s: multiset<T>, w: T)
        requires w in s
        requires forall y :: y in s ==> R(w, y)
        ensures exists m :: m in s && forall y :: y in s ==> R(m, y)
    {}

    // For any total ordering R, a non-empty set has an R-minimum element.
    lemma ThereIsAMinimum<T(!new)>(R: (T, T) -> bool, s: set<T>)
        requires s != {}
        requires TotalOrdering(R)
        ensures exists m :: m in s && forall y :: y in s ==> R(m, y)
        decreases s
    {
        var x :| x in s;
        if s == {x} {
            assert forall y :: y in s ==> R(x, y) by {
                forall y | y in s ensures R(x, y) { assert R(x, x); }   // Reflexive
            }
            MinWitnessSet(R, s, x);
        } else {
            var s' := s - {x};
            ThereIsAMinimum(R, s');
            var y :| y in s' && forall z :: z in s' ==> R(y, z);
            if R(y, x) {
                assert forall z :: z in s ==> R(y, z) by {
                    forall z | z in s ensures R(y, z) { if z != x { assert z in s'; } }
                }
                MinWitnessSet(R, s, y);
            } else {
                assert R(x, y);   // StronglyConnected: !R(y, x) ==> R(x, y)
                assert forall z :: z in s ==> R(x, z) by {
                    forall z | z in s ensures R(x, z) {
                        if z == x { assert R(x, x); }
                        else { assert z in s'; assert R(y, z); }   // Transitive
                    }
                }
                MinWitnessSet(R, s, x);
            }
        }
    }

    // Same, for multisets.
    lemma ThereIsAMinimumMultiset<T(!new)>(R: (T, T) -> bool, s: multiset<T>)
        requires s != multiset{}
        requires TotalOrdering(R)
        ensures exists m :: m in s && forall y :: y in s ==> R(m, y)
        decreases |s|
    {
        var x :| x in s;
        var s' := s[x := 0];
        if s' == multiset{} {
            assert forall y :: y in s ==> R(x, y) by {
                forall y | y in s ensures R(x, y) {
                    if y != x { assert y in s'; }   // s' empty, contradiction
                    else { assert R(x, x); }        // Reflexive
                }
            }
            MinWitnessMultiset(R, s, x);
        } else {
            assert |s'| < |s|;
            ThereIsAMinimumMultiset(R, s');
            var y :| y in s' && forall z :: z in s' ==> R(y, z);
            assert y in s;
            if R(y, x) {
                assert forall z :: z in s ==> R(y, z) by {
                    forall z | z in s ensures R(y, z) { if z != x { assert z in s'; } }
                }
                MinWitnessMultiset(R, s, y);
            } else {
                assert R(x, y);   // StronglyConnected: !R(y, x) ==> R(x, y)
                assert forall z :: z in s ==> R(x, z) by {
                    forall z | z in s ensures R(x, z) {
                        if z == x { assert R(x, x); }
                        else { assert z in s'; assert R(y, z); }   // Transitive
                    }
                }
                MinWitnessMultiset(R, s, x);
            }
        }
    }

    // Deterministic fold over a set: peels off the R-minimum element each step,
    // which is unique under a total ordering, so the result is well defined.
    function SetFold<T(!new), U>(R: (T, T) -> bool, xs: set<T>, f: (T, U) -> U, init: U): U
        requires TotalOrdering(R)
    {
        if xs == {} then init
        else
            ThereIsAMinimum(R, xs);
            var x :| x in xs && forall z :: z in xs ==> R(x, z);
            SetFold(R, xs-{x}, f, f(x, init))
    }

    function MultisetFold<T(!new), U>(R: (T, T) -> bool, xs: multiset<T>, f: (T, U) -> U, init: U): U
        requires TotalOrdering(R)
        decreases |xs|
    {
        if xs == multiset{} then init
        else
            ThereIsAMinimumMultiset(R, xs);
            var x :| x in xs && forall z :: z in xs ==> R(x, z);
            assert |xs[x := 0]| < |xs|;
            MultisetFold(R, xs[x := 0], f, f(x, init))
    }

    // The usual ordering on naturals, packaged as a relation value.
    predicate NatLe(a: nat, b: nat) { a <= b }

    lemma NatLeOrdering()
        ensures TotalOrdering(NatLe)
    {}

    // Sum of a set of naturals. Peels off the R-minimum element so the pick is
    // unique (hence compilable); SumSetRemove shows the value is independent of
    // which element is removed (so the ordering R only fixes the recursion, not
    // the result). Callers pass a total ordering such as NatLe.
    function SumSet(R: (nat, nat) -> bool, s: set<nat>): nat
        requires TotalOrdering(R)
    {
        if s == {} then 0
        else
            ThereIsAMinimum(R, s);
            var m :| m in s && forall z :: z in s ==> R(m, z);
            m + SumSet(R, s - {m})
    }

    lemma SumSetRemove(R: (nat, nat) -> bool, s: set<nat>, y: nat)
        requires TotalOrdering(R)
        requires y in s
        ensures SumSet(R, s) == y + SumSet(R, s - {y})
        decreases s
    {
        ThereIsAMinimum(R, s);
        var m :| m in s && forall z :: z in s ==> R(m, z);
        assert SumSet(R, s) == m + SumSet(R, s - {m});   // matches SumSet's own pick
        if y != m {
            SumSetRemove(R, s - {m}, y);   // SumSet(s-{m}) == y + SumSet(s-{m}-{y})
            SumSetRemove(R, s - {y}, m);   // SumSet(s-{y}) == m + SumSet(s-{y}-{m})
            assert s - {m} - {y} == s - {y} - {m};
        }
    }

    lemma SumSetInsert(R: (nat, nat) -> bool, s: set<nat>, x: nat)
        requires TotalOrdering(R)
        requires x !in s
        ensures SumSet(R, s + {x}) == SumSet(R, s) + x
    {
        SumSetRemove(R, s + {x}, x);
        assert (s + {x}) - {x} == s;
    }
}
