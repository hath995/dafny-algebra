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

// Fully concrete: ideals of the integers, with the (possibly infinite) iset carrier.
module IntIdeals refines Ideals {
    import R = IntRing
    import L = ISetColl

    // The principal ideal (n) = nZ = { n*k : k in Z }. Every ideal of Z is of this
    // form -- Z is a principal ideal domain -- and quotienting by it gives Z/nZ.
    lemma MultiplesIdeal(n: int)
        ensures IsIdeal(iset x: int | exists k :: x == n * k)
    {
        var s := iset x: int | exists k :: x == n * k;
        assert 0 == n * 0;                                   // 0 in (n)
        forall a, b | L.In(a, s) && L.In(b, s)
            ensures L.In(R.op(a, b), s)
        {
            var ka :| a == n * ka;
            var kb :| b == n * kb;
            assert a + b == n * (ka + kb);                   // closure under +
        }
        forall a | L.In(a, s)
            ensures L.In(R.Inv(a), s)
        {
            var ka :| a == n * ka;
            assert -a == n * (-ka);                          // closure under negation
        }
        forall r, a | L.In(a, s)
            ensures L.In(R.mul(r, a), s)
        {
            var ka :| a == n * ka;
            assert r * a == n * (r * ka);                    // absorption: r*(n*ka) == n*(r*ka)
        }
    }

    // The even integers 2Z, the kernel of Z -> Z/2Z.
    lemma EvensIdeal()
        ensures IsIdeal(iset x: int | exists k :: x == 2 * k)
    {
        MultiplesIdeal(2);
    }
}

// The quotient ring Z/6Z == Z / (6Z): the integers modulo the principal ideal 6Z
// (see IntIdeals.MultiplesIdeal(6)). It is a commutative ring, and a witness that
// quotienting by a NON-prime modulus loses the integral-domain property: 2*3 == 0
// although neither factor is zero -- 2 and 3 are zero divisors.
module ZMod6Ring refines CommRing {
    type T = x: int | 0 <= x < 6
    function op(a: T, b: T): T { (a + b) % 6 }
    function Id(): T { 0 }
    function Inv(a: T): T { (6 - a) % 6 }
    function mul(a: T, b: T): T { (a * b) % 6 }
    function One(): T { 1 }

    // ---- self-contained mod-6 congruences (no standard library) ----
    // Adding a multiple of 6 leaves the residue unchanged (Dafny proves it directly).
    lemma AddMultiple(r: int, k: int)
        ensures (r + 6 * k) % 6 == r % 6
    {}
    // Reducing the left factor before multiplying does not change the residue.
    lemma ModMulLeft(x: int, y: int)
        ensures ((x % 6) * y) % 6 == (x * y) % 6
    {
        var q := x / 6;
        assert x == 6 * q + x % 6;                  // div/mod identity
        assert x * y == (x % 6) * y + 6 * (q * y);  // distribute y
        AddMultiple((x % 6) * y, q * y);
    }
    lemma ModMulRight(x: int, y: int)
        ensures (x * (y % 6)) % 6 == (x * y) % 6
    {
        var q := y / 6;
        assert y == 6 * q + y % 6;
        assert x * y == x * (y % 6) + 6 * (x * q);
        AddMultiple(x * (y % 6), x * q);
    }
    // Reducing both summands before adding does not change the residue (automatic).
    lemma AddModBoth(x: int, y: int)
        ensures ((x % 6) + (y % 6)) % 6 == (x + y) % 6
    {}

    // Additive abelian group laws (mod-6 addition) -- discharged automatically.
    lemma Assoc(a: T, b: T, c: T) {}
    lemma LeftId(a: T) {}
    lemma RightId(a: T) {}
    lemma LeftInv(a: T) {}
    lemma RightInv(a: T) {}
    lemma Comm(a: T, b: T) {}

    // Multiplicative monoid + distributivity, via the mod congruences above.
    lemma MulAssoc(a: T, b: T, c: T) {
        ModMulLeft(a * b, c);    // ((a*b)%6 * c)%6 == ((a*b)*c)%6
        ModMulRight(a, b * c);   // (a * (b*c)%6)%6 == (a*(b*c))%6
        assert (a * b) * c == a * (b * c);
    }
    lemma MulLeftId(a: T) {}
    lemma MulRightId(a: T) {}
    lemma LeftDistrib(a: T, b: T, c: T) {
        ModMulRight(a, b + c);   // (a * (b+c)%6)%6 == (a*(b+c))%6
        AddModBoth(a * b, a * c); // ((a*b)%6 + (a*c)%6)%6 == (a*b + a*c)%6
        assert a * (b + c) == a * b + a * c;
    }
    lemma RightDistrib(a: T, b: T, c: T) {
        ModMulLeft(a + b, c);    // ((a+b)%6 * c)%6 == ((a+b)*c)%6
        AddModBoth(a * c, b * c); // ((a*c)%6 + (b*c)%6)%6 == (a*c + b*c)%6
        assert (a + b) * c == a * c + b * c;
    }
    lemma MulComm(a: T, b: T) {}

    // The defining feature of this quotient: it has zero divisors, so unlike Z
    // (IntRing, an integral domain) it is NOT an integral domain.
    lemma HasZeroDivisors()
        ensures mul(2, 3) == Id() && 2 != Id() && 3 != Id()
    {}
}
