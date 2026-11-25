include "../src/ideals.dfy"

// DEMOS of the abstract ideal theory in src/ideals.dfy: the principal ideals of
// the integers, and the quotient ring Z/6Z. Concrete/specific instantiations,
// moved out of src/ so the library proper keeps only the generic theory.

// Fully concrete: ideals of the integers, with the (possibly infinite) iset carrier.
module IntIdeals refines Ideals {
    import R = IntRing
    import L = ISetColl

    // Membership predicate for the principal ideal (n) = nZ, named so the set
    // comprehensions have an explicit trigger (an inline `exists` has none).
    ghost predicate IsMultiple(x: int, n: int) { exists k :: x == n * k }

    // The principal ideal (n) = nZ = { n*k : k in Z }. Every ideal of Z is of this
    // form -- Z is a principal ideal domain -- and quotienting by it gives Z/nZ.
    lemma MultiplesIdeal(n: int)
        ensures IsIdeal(iset x: int | IsMultiple(x, n))
    {
        var s := iset x: int | IsMultiple(x, n);
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
        ensures IsIdeal(iset x: int | IsMultiple(x, 2))
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
