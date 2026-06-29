// The algebraic hierarchy as a chain of abstract modules.
//
// Dafny modules support single refinement only, so the hierarchy is a LINEAR
// chain along one operation:
//
//     Magma -> Semigroup -> Monoid -> Group -> AbelianGroup
//
// Each step adds one law. Laws are body-less lemmas in the abstract modules;
// a concrete instance discharges them (usually with an empty body, since the
// verifier proves int/real arithmetic facts automatically).
//
// A Ring is the place the single-parent rule bites: it is an additive abelian
// group AND a multiplicative monoid at once. There is no multiple inheritance,
// so Ring refines the additive AbelianGroup and *inlines* the multiplicative
// structure (mul, One, its associativity/identity) plus distributivity.

abstract module Magma {
    type T(==, !new)
    function op(a: T, b: T): T
}

abstract module Semigroup refines Magma {
    lemma Assoc(a: T, b: T, c: T)
        ensures op(op(a, b), c) == op(a, op(b, c))

    // Generalised associativity: any bracketing of a chain is equal.
    lemma Assoc4(a: T, b: T, c: T, d: T)
        ensures op(op(op(a, b), c), d) == op(a, op(b, op(c, d)))
    {
        Assoc(a, b, c);
        Assoc(a, op(b, c), d);
        Assoc(b, c, d);
    }
}

abstract module Monoid refines Semigroup {
    function Id(): T
    lemma LeftId(a: T) ensures op(Id(), a) == a
    lemma RightId(a: T) ensures op(a, Id()) == a

    // The identity is unique: any left identity must be Id().
    lemma IdentityUnique(e: T)
        requires forall a :: op(e, a) == a
        ensures e == Id()
    {
        assert op(e, Id()) == Id();   // hypothesis at a == Id()
        RightId(e);                   // op(e, Id()) == e
    }

    // ---- powers: a^n = a op a op ... op a (n times), a^0 = Id() ----
    function pow(a: T, n: nat): T {
        if n == 0 then Id() else op(pow(a, n-1), a)
    }

    lemma Pow1(a: T)
        ensures pow(a, 1) == a
    {
        LeftId(a);   // pow(a,1) == op(Id(), a) == a
    }

    // a^(n+k) == a^n op a^k   (ports apowAddition)
    lemma PowAdd(a: T, n: nat, k: nat)
        ensures pow(a, n + k) == op(pow(a, n), pow(a, k))
        decreases k
    {
        if k == 0 {
            RightId(pow(a, n));
        } else {
            PowAdd(a, n, k-1);
            Assoc(pow(a, n), pow(a, k-1), a);
        }
    }

    // An element commutes with its own powers: a op a^n == a^(n+1).
    lemma PowLeft(a: T, n: nat)
        ensures op(a, pow(a, n)) == pow(a, n + 1)
    {
        PowAdd(a, 1, n);
        Pow1(a);
    }

    // (a^n)^k == a^(n*k)   (ports apowExponent)
    lemma PowMul(a: T, n: nat, k: nat)
        ensures pow(a, n * k) == pow(pow(a, n), k)
        decreases k
    {
        if k != 0 {
            PowMul(a, n, k-1);
            PowAdd(a, n * (k-1), n);
            assert n * k == n * (k-1) + n;
        }
    }
}

abstract module Group refines Monoid {
    function Inv(a: T): T
    lemma LeftInv(a: T) ensures op(Inv(a), a) == Id()
    lemma RightInv(a: T) ensures op(a, Inv(a)) == Id()

    // Cancellation laws.
    lemma LeftCancel(a: T, b: T, c: T)
        requires op(a, b) == op(a, c)
        ensures b == c
    {
        calc {
            b;
            { LeftId(b); }
            op(Id(), b);
            { LeftInv(a); }
            op(op(Inv(a), a), b);
            { Assoc(Inv(a), a, b); }
            op(Inv(a), op(a, b));
            op(Inv(a), op(a, c));
            { Assoc(Inv(a), a, c); }
            op(op(Inv(a), a), c);
            { LeftInv(a); }
            op(Id(), c);
            { LeftId(c); }
            c;
        }
    }

    lemma RightCancel(a: T, b: T, c: T)
        requires op(b, a) == op(c, a)
        ensures b == c
    {
        calc {
            b;
            { RightId(b); }
            op(b, Id());
            { RightInv(a); }
            op(b, op(a, Inv(a)));
            { Assoc(b, a, Inv(a)); }
            op(op(b, a), Inv(a));
            op(op(c, a), Inv(a));
            { Assoc(c, a, Inv(a)); }
            op(c, op(a, Inv(a)));
            { RightInv(a); }
            op(c, Id());
            { RightId(c); }
            c;
        }
    }

    // Inverses are unique (either side determines Inv).
    lemma InvUnique(x: T, c: T)
        requires op(c, x) == Id()
        ensures c == Inv(x)
    {
        LeftInv(x);
        RightCancel(x, c, Inv(x));
    }

    lemma InvUniqueRight(x: T, c: T)
        requires op(x, c) == Id()
        ensures c == Inv(x)
    {
        RightInv(x);
        LeftCancel(x, c, Inv(x));
    }

    lemma InvInv(a: T)
        ensures Inv(Inv(a)) == a
    {
        RightInv(a);
        InvUnique(Inv(a), a);
    }

    lemma InvId()
        ensures Inv(Id()) == Id()
    {
        LeftId(Id());
        InvUnique(Id(), Id());
    }

    // Inverse of a product reverses the order.
    lemma InvOp(a: T, b: T)
        ensures Inv(op(a, b)) == op(Inv(b), Inv(a))
    {
        calc {
            op(op(Inv(b), Inv(a)), op(a, b));
            { Assoc(Inv(b), Inv(a), op(a, b)); }
            op(Inv(b), op(Inv(a), op(a, b)));
            { Assoc(Inv(a), a, b); }
            op(Inv(b), op(op(Inv(a), a), b));
            { LeftInv(a); }
            op(Inv(b), op(Id(), b));
            { LeftId(b); }
            op(Inv(b), b);
            { LeftInv(b); }
            Id();
        }
        InvUnique(op(a, b), op(Inv(b), Inv(a)));
    }

    // (a^n)^-1 == (a^-1)^n   (ports apowInverse)
    lemma PowInv(a: T, n: nat)
        ensures Inv(pow(a, n)) == pow(Inv(a), n)
        decreases n
    {
        if n == 0 {
            InvId();
        } else {
            PowInv(a, n-1);
            InvOp(pow(a, n-1), a);   // Inv(a^n) == op(Inv(a), Inv(a^(n-1)))
            PowLeft(Inv(a), n-1);    // op(Inv(a), (a^-1)^(n-1)) == (a^-1)^n
        }
    }

    // a^-1 op a^n == a^(n-1)   (ports apowSubtract)
    lemma PowSubtract(a: T, n: nat)
        requires n >= 1
        ensures op(Inv(a), pow(a, n)) == pow(a, n-1)
    {
        PowLeft(a, n-1);                    // a^n == op(a, a^(n-1))
        Assoc(Inv(a), a, pow(a, n-1));
        LeftInv(a);
        LeftId(pow(a, n-1));
    }
}

abstract module AbelianGroup refines Group {
    lemma Comm(a: T, b: T) ensures op(a, b) == op(b, a)

    // In a commutative group the inverse of a product keeps the order.
    lemma InvOpAbelian(a: T, b: T)
        ensures Inv(op(a, b)) == op(Inv(a), Inv(b))
    {
        InvOp(a, b);
        Comm(Inv(b), Inv(a));
    }
}

// op/Id/Inv are the ADDITIVE abelian group; the multiplicative monoid is
// inlined here because we cannot also `refines Monoid`.
abstract module Ring refines AbelianGroup {
    function mul(a: T, b: T): T
    function One(): T
    lemma MulAssoc(a: T, b: T, c: T) ensures mul(mul(a, b), c) == mul(a, mul(b, c))
    lemma MulLeftId(a: T) ensures mul(One(), a) == a
    lemma MulRightId(a: T) ensures mul(a, One()) == a
    lemma LeftDistrib(a: T, b: T, c: T) ensures mul(a, op(b, c)) == op(mul(a, b), mul(a, c))
    lemma RightDistrib(a: T, b: T, c: T) ensures mul(op(a, b), c) == op(mul(a, c), mul(b, c))

    // Zero (the additive identity) annihilates under multiplication. Needs the
    // additive group's cancellation — the reason this lives in Ring, not Monoid.
    lemma MulZeroLeft(x: T)
        ensures mul(Id(), x) == Id()
    {
        LeftId(Id());                  // op(Id, Id) == Id
        RightDistrib(Id(), Id(), x);   // mul(op(Id,Id), x) == op(mul(Id,x), mul(Id,x))
        var m := mul(Id(), x);
        assert m == op(m, m);
        RightId(m);
        LeftCancel(m, Id(), m);
    }

    lemma MulZeroRight(x: T)
        ensures mul(x, Id()) == Id()
    {
        LeftId(Id());
        LeftDistrib(x, Id(), Id());    // mul(x, op(Id,Id)) == op(mul(x,Id), mul(x,Id))
        var m := mul(x, Id());
        assert m == op(m, m);
        RightId(m);
        LeftCancel(m, Id(), m);
    }

    // Negation pulls through multiplication: (-a) * b == -(a * b).
    lemma MulNegLeft(a: T, b: T)
        ensures mul(Inv(a), b) == Inv(mul(a, b))
    {
        RightDistrib(a, Inv(a), b);    // mul(op(a,Inv(a)), b) == op(mul(a,b), mul(Inv(a),b))
        RightInv(a);                   // op(a, Inv(a)) == Id()
        MulZeroLeft(b);                // mul(Id(), b) == Id()
        InvUniqueRight(mul(a, b), mul(Inv(a), b));
    }

    // ...and on the right too: a * (-b) == -(a * b).
    lemma MulNegRight(a: T, b: T)
        ensures mul(a, Inv(b)) == Inv(mul(a, b))
    {
        LeftDistrib(a, b, Inv(b));     // mul(a, op(b,Inv(b))) == op(mul(a,b), mul(a,Inv(b)))
        RightInv(b);                   // op(b, Inv(b)) == Id()
        MulZeroRight(a);               // mul(a, Id()) == Id()
        InvUniqueRight(mul(a, b), mul(a, Inv(b)));
    }
}

abstract module CommRing refines Ring {
    lemma MulComm(a: T, b: T) ensures mul(a, b) == mul(b, a)
}

// An integral domain sits between a commutative ring and a field: it is a
// commutative ring with NO zero divisors (a product is zero only if a factor
// is). This is the missing rung that lets the integers be classified exactly --
// IntRing is an integral domain but not a field. NoZeroDivisors is an AXIOM here
// (there is no multiplicative inverse to derive it from, as Field does); the
// payoff is multiplicative cancellation, derived once below.
abstract module IntegralDomain refines CommRing {
    lemma NoZeroDivisors(a: T, b: T)
        requires mul(a, b) == Id()
        ensures a == Id() || b == Id()

    // Cancel a nonzero common factor: a != 0 and a*b == a*c forces b == c.
    // (False in a ring with zero divisors -- e.g. 2*1 == 2*4 in Z/6Z.)
    lemma MulCancel(a: T, b: T, c: T)
        requires a != Id()
        requires mul(a, b) == mul(a, c)
        ensures b == c
    {
        var d := op(b, Inv(c));
        calc {
            mul(a, d);
            { LeftDistrib(a, b, Inv(c)); }
            op(mul(a, b), mul(a, Inv(c)));
            { MulNegRight(a, c); }              // mul(a, Inv(c)) == Inv(mul(a,c))
            op(mul(a, b), Inv(mul(a, c)));
            op(mul(a, c), Inv(mul(a, c)));      // mul(a,b) == mul(a,c)
            { RightInv(mul(a, c)); }
            Id();
        }
        NoZeroDivisors(a, d);                   // a != Id(), so d == Id()
        InvUniqueRight(b, Inv(c));              // op(b, Inv(c)) == Id() ==> Inv(c) == Inv(b)
        InvInv(b);
        InvInv(c);                              // c == Inv(Inv(c)) == Inv(Inv(b)) == b
    }
}

// A field adds multiplicative inverses for everything except the additive
// identity (Id() == 0). Every field is an integral domain (proved: the
// NoZeroDivisors axiom is discharged here from MulInv).
abstract module Field refines IntegralDomain {
    function MulInv(a: T): T
    lemma MulLeftInv(a: T) requires a != Id() ensures mul(MulInv(a), a) == One()

    // The multiplicative inverse works on the right too (commutativity).
    lemma MulRightInv(a: T)
        requires a != Id()
        ensures mul(a, MulInv(a)) == One()
    {
        MulLeftInv(a);
        MulComm(a, MulInv(a));
    }

    // A field has no zero divisors: discharges IntegralDomain's axiom, proving
    // a product is zero only if a factor is (spec inherited from the parent).
    lemma NoZeroDivisors(a: T, b: T)
    {
        if a != Id() {
            calc {
                b;
                { MulLeftId(b); }
                mul(One(), b);
                { MulLeftInv(a); }
                mul(mul(MulInv(a), a), b);
                { MulAssoc(MulInv(a), a, b); }
                mul(MulInv(a), mul(a, b));
                mul(MulInv(a), Id());
                { MulZeroRight(MulInv(a)); }
                Id();
            }
        }
    }
}

// ---- concrete instances ----

// The integers are an integral domain (a commutative ring with no zero
// divisors) -- but NOT a field, since only +-1 have integer inverses.
module IntRing refines IntegralDomain {
    type T = int
    function op(a: T, b: T): T { a + b }
    function Id(): T { 0 }
    function Inv(a: T): T { -a }
    function mul(a: T, b: T): T { a * b }
    function One(): T { 1 }

    lemma Assoc(a: T, b: T, c: T) {}
    lemma LeftId(a: T) {}
    lemma RightId(a: T) {}
    lemma LeftInv(a: T) {}
    lemma RightInv(a: T) {}
    lemma Comm(a: T, b: T) {}
    lemma MulAssoc(a: T, b: T, c: T) {}
    lemma MulLeftId(a: T) {}
    lemma MulRightId(a: T) {}
    lemma LeftDistrib(a: T, b: T, c: T) {}
    lemma RightDistrib(a: T, b: T, c: T) {}
    lemma MulComm(a: T, b: T) {}
    lemma NoZeroDivisors(a: T, b: T) {}   // a*b == 0 ==> a == 0 || b == 0, over Z
}

// The reals are a field.
module RealField refines Field {
    type T = real
    function op(a: T, b: T): T { a + b }
    function Id(): T { 0.0 }
    function Inv(a: T): T { -a }
    function mul(a: T, b: T): T { a * b }
    function One(): T { 1.0 }
    function MulInv(a: T): T { if a == 0.0 then 0.0 else 1.0 / a }   // total; value at 0 is unused

    lemma Assoc(a: T, b: T, c: T) {}
    lemma LeftId(a: T) {}
    lemma RightId(a: T) {}
    lemma LeftInv(a: T) {}
    lemma RightInv(a: T) {}
    lemma Comm(a: T, b: T) {}
    lemma MulAssoc(a: T, b: T, c: T) {}
    lemma MulLeftId(a: T) {}
    lemma MulRightId(a: T) {}
    lemma LeftDistrib(a: T, b: T, c: T) {}
    lemma RightDistrib(a: T, b: T, c: T) {}
    lemma MulComm(a: T, b: T) {}
    lemma MulLeftInv(a: T) {}   // (1/a) * a == 1 for a != 0
}
