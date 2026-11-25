include "algebra.dfy"
include "collections.dfy"

// Ideal theory, parameterized -- exactly like Subgroups -- by BOTH the ring
// (import R) and the collection type (import L), so the theory is written once
// and reused for finite (set) and infinite (iset) carriers. An ideal is the ring
// analogue of a normal subgroup: it is precisely what one can quotient a ring by.
abstract module Ideals {
    import R : CommRing
    import L : Collection

    // An ideal: an additive subgroup of (R, +) that also ABSORBS multiplication
    // by any ring element (r*a stays in the ideal). R is commutative, so the one
    // absorption law covers both sides.
    ghost predicate IsIdeal(s: L.C<R.T>) {
        && L.In(R.Id(), s)
        && (forall a, b :: L.In(a, s) && L.In(b, s) ==> L.In(R.op(a, b), s))
        && (forall a :: L.In(a, s) ==> L.In(R.Inv(a), s))
        && (forall r, a :: L.In(a, s) ==> L.In(R.mul(r, a), s))
    }

    // The zero ideal {0}: r*0 == 0, so absorption holds. (Written once; serves the
    // set and iset instantiations alike.)
    lemma ZeroIdeal()
        ensures IsIdeal(L.Single(R.Id()))
    {
        L.SingleChar(R.Id(), R.Id());
        R.LeftId(R.Id());
        R.InvId();
        forall a, b | L.In(a, L.Single(R.Id())) && L.In(b, L.Single(R.Id()))
            ensures L.In(R.op(a, b), L.Single(R.Id()))
        {
            L.SingleChar(R.Id(), a);
            L.SingleChar(R.Id(), b);
            L.SingleChar(R.Id(), R.op(a, b));
        }
        forall a | L.In(a, L.Single(R.Id()))
            ensures L.In(R.Inv(a), L.Single(R.Id()))
        {
            L.SingleChar(R.Id(), a);
            L.SingleChar(R.Id(), R.Inv(a));
        }
        forall r, a | L.In(a, L.Single(R.Id()))
            ensures L.In(R.mul(r, a), L.Single(R.Id()))
        {
            L.SingleChar(R.Id(), a);          // a == 0
            R.MulZeroRight(r);                // mul(r, 0) == 0
            L.SingleChar(R.Id(), R.mul(r, a));
        }
    }

    // The intersection of two ideals is an ideal.
    lemma IdealIntersect(s: L.C<R.T>, t: L.C<R.T>)
        requires IsIdeal(s) && IsIdeal(t)
        ensures IsIdeal(L.Inter(s, t))
    {
        L.InterChar(s, t, R.Id());
        forall a, b | L.In(a, L.Inter(s, t)) && L.In(b, L.Inter(s, t))
            ensures L.In(R.op(a, b), L.Inter(s, t))
        {
            L.InterChar(s, t, a);
            L.InterChar(s, t, b);
            L.InterChar(s, t, R.op(a, b));
        }
        forall a | L.In(a, L.Inter(s, t))
            ensures L.In(R.Inv(a), L.Inter(s, t))
        {
            L.InterChar(s, t, a);
            L.InterChar(s, t, R.Inv(a));
        }
        forall r, a | L.In(a, L.Inter(s, t))
            ensures L.In(R.mul(r, a), L.Inter(s, t))
        {
            L.InterChar(s, t, a);
            L.InterChar(s, t, R.mul(r, a));
        }
    }

    // An ideal is closed under (natural) multiples n*a (a folded into itself n
    // times by addition), since each step adds an element already in the ideal.
    lemma IdealClosedUnderPow(s: L.C<R.T>, a: R.T, n: nat)
        requires IsIdeal(s) && L.In(a, s)
        ensures L.In(R.pow(a, n), s)
        decreases n
    {
        if n == 0 {
            // pow(a,0) == Id(), which is in every ideal.
        } else {
            IdealClosedUnderPow(s, a, n - 1);   // a^(n-1) and a in s, so op(a^(n-1), a) in s
        }
    }
}
