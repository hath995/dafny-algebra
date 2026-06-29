include "algebra.dfy"

// A semiring: like a ring but WITHOUT additive inverses. It refines the additive
// Monoid (op = +, Id() = 0), declares that addition is commutative, and inlines a
// multiplicative monoid (mul, One) tied to addition by distributivity -- exactly
// the shape of `Ring` in algebra.dfy. The one structural difference: in a ring,
// 0*a == 0 is DERIVED from the additive inverse; with no inverse here it must be
// an AXIOM (MulZeroLeft/Right).
abstract module Semiring refines Monoid {
    // Inherited additive monoid: op (= +), Id (= 0), Assoc, LeftId, RightId, pow.
    lemma Comm(a: T, b: T)
        ensures op(a, b) == op(b, a)

    // Multiplicative monoid, inlined.
    function mul(a: T, b: T): T
    function One(): T
    lemma MulAssoc(a: T, b: T, c: T)
        ensures mul(mul(a, b), c) == mul(a, mul(b, c))
    lemma MulLeftId(a: T)
        ensures mul(One(), a) == a
    lemma MulRightId(a: T)
        ensures mul(a, One()) == a

    // Multiplication distributes over addition (both sides; addition is commutative
    // but multiplication need not be, so we keep both laws).
    lemma LeftDistrib(a: T, b: T, c: T)
        ensures mul(a, op(b, c)) == op(mul(a, b), mul(a, c))
    lemma RightDistrib(a: T, b: T, c: T)
        ensures mul(op(a, b), c) == op(mul(a, c), mul(b, c))

    // Zero annihilates -- an axiom here, since there is no additive inverse to
    // cancel with (this is what `Ring` gets to prove instead of assume).
    lemma MulZeroLeft(a: T)
        ensures mul(Id(), a) == Id()
    lemma MulZeroRight(a: T)
        ensures mul(a, Id()) == Id()

    // Derived: the FOIL expansion, from distributivity alone.
    // (a + b)(c + d) == (ac + ad) + (bc + bd).
    lemma MulDistribBoth(a: T, b: T, c: T, d: T)
        ensures mul(op(a, b), op(c, d))
             == op(op(mul(a, c), mul(a, d)), op(mul(b, c), mul(b, d)))
    {
        RightDistrib(a, b, op(c, d));   // (a+b)(c+d) == a(c+d) + b(c+d)
        LeftDistrib(a, c, d);           // a(c+d) == ac + ad
        LeftDistrib(b, c, d);           // b(c+d) == bc + bd
    }
}

// The naturals (0,1,+,*): the prototypical semiring (no additive inverses).
module NatSemiring refines Semiring {
    type T = nat
    function op(a: T, b: T): T { a + b }
    function Id(): T { 0 }
    function mul(a: T, b: T): T { a * b }
    function One(): T { 1 }

    lemma Assoc(a: T, b: T, c: T) {}
    lemma LeftId(a: T) {}
    lemma RightId(a: T) {}
    lemma Comm(a: T, b: T) {}
    lemma MulAssoc(a: T, b: T, c: T) {}
    lemma MulLeftId(a: T) {}
    lemma MulRightId(a: T) {}
    lemma LeftDistrib(a: T, b: T, c: T) {}
    lemma RightDistrib(a: T, b: T, c: T) {}
    lemma MulZeroLeft(a: T) {}
    lemma MulZeroRight(a: T) {}
}

// The Boolean semiring (OR as +, AND as *): false = 0, true = 1. Idempotent.
module BoolSemiring refines Semiring {
    type T = bool
    function op(a: T, b: T): T { a || b }
    function Id(): T { false }
    function mul(a: T, b: T): T { a && b }
    function One(): T { true }

    lemma Assoc(a: T, b: T, c: T) {}
    lemma LeftId(a: T) {}
    lemma RightId(a: T) {}
    lemma Comm(a: T, b: T) {}
    lemma MulAssoc(a: T, b: T, c: T) {}
    lemma MulLeftId(a: T) {}
    lemma MulRightId(a: T) {}
    lemma LeftDistrib(a: T, b: T, c: T) {}
    lemma RightDistrib(a: T, b: T, c: T) {}
    lemma MulZeroLeft(a: T) {}
    lemma MulZeroRight(a: T) {}
}

// The tropical (min, +) semiring. Addition is min with identity +infinity (the
// semiring's zero), multiplication is ordinary + with identity 0. Its matrix
// product computes all-pairs shortest paths -- the Floyd-Warshall algebra.
module Tropical refines Semiring {
    datatype Trop = Inf | Fin(v: int)
    type T = Trop

    function op(a: T, b: T): T {          // tropical addition == min
        match a
        case Inf => b
        case Fin(x) => (match b case Inf => a case Fin(y) => Fin(if x <= y then x else y))
    }
    function Id(): T { Inf }               // additive identity == +infinity

    function mul(a: T, b: T): T {          // tropical multiplication == ordinary +
        match a
        case Inf => Inf
        case Fin(x) => (match b case Inf => Inf case Fin(y) => Fin(x + y))
    }
    function One(): T { Fin(0) }           // multiplicative identity == 0

    lemma Assoc(a: T, b: T, c: T) {}       // min is associative
    lemma LeftId(a: T) {}
    lemma RightId(a: T) {}
    lemma Comm(a: T, b: T) {}              // min is commutative
    lemma MulAssoc(a: T, b: T, c: T) {}    // + is associative
    lemma MulLeftId(a: T) {}
    lemma MulRightId(a: T) {}
    lemma LeftDistrib(a: T, b: T, c: T) {}     // a + min(b,c) == min(a+b, a+c)
    lemma RightDistrib(a: T, b: T, c: T) {}
    lemma MulZeroLeft(a: T) {}             // Inf + a == Inf
    lemma MulZeroRight(a: T) {}

    // Order facts: tropical addition (min) is idempotent, so it is a semilattice and
    // this semiring is a DIOID. With x <= y :<==> op(x,y) == x, these say min picks
    // one argument and is a lower bound on both -- exactly what the shortest-path
    // reading of a matrix product needs.
    lemma OpIdem(a: T) ensures op(a, a) == a {}
    lemma OpPicks(a: T, b: T) ensures op(a, b) == a || op(a, b) == b {}
    lemma LeqLeft(a: T, b: T) ensures op(op(a, b), a) == op(a, b) {}    // min(a,b) <= a
    lemma LeqRight(a: T, b: T) ensures op(op(a, b), b) == op(a, b) {}   // min(a,b) <= b
    lemma LeqTrans(a: T, b: T, c: T)
        requires op(a, b) == a && op(b, c) == b
        ensures op(a, c) == a
    {}

    // Multiplication (tropical +) is monotone in the order: x <= y ==> a+x <= a+y.
    // This is what lets one extra edge preserve a shortest-path bound.
    lemma MulMono(a: T, x: T, y: T)
        requires op(x, y) == x
        ensures op(mul(a, x), mul(a, y)) == mul(a, x)
    {}
}

// A star semiring (closed semiring): a semiring with a unary `star` obeying the
// two fixpoint-unfolding laws  a* == 1 + a*(a*) == 1 + (a*)*a. Reading op as
// "alternation/union of paths" and mul as "concatenation", a* is "zero or more
// copies of a" -- the reflexive-transitive-closure operator behind Kleene's
// theorem and behind iterating the matrix product in matrices_over_semiring.dfy.
abstract module StarSemiring refines Semiring {
    function star(a: T): T

    lemma StarUnfoldLeft(a: T)
        ensures star(a) == op(One(), mul(a, star(a)))
    lemma StarUnfoldRight(a: T)
        ensures star(a) == op(One(), mul(star(a), a))

    // The star of zero is one: 0* == 1 + 0*(0*) == 1 + 0 == 1. (Derived from the
    // left-unfold law together with the semiring's annihilation and identity.)
    lemma StarZero()
        ensures star(Id()) == One()
    {
        StarUnfoldLeft(Id());        // 0* == op(1, mul(0, 0*))
        MulZeroLeft(star(Id()));     // mul(0, 0*) == 0
        RightId(One());              // op(1, 0) == 1
    }
}

// The Boolean star semiring: in (OR, AND) the star of anything is true, since
// a* == 1 OR (a AND a*) == true. This is reachability collapsed to one bit --
// "is there a path?" -- the scalar shadow of transitive closure.
module BoolStarSemiring refines StarSemiring {
    type T = bool
    function op(a: T, b: T): T { a || b }
    function Id(): T { false }
    function mul(a: T, b: T): T { a && b }
    function One(): T { true }
    function star(a: T): T { true }

    lemma Assoc(a: T, b: T, c: T) {}
    lemma LeftId(a: T) {}
    lemma RightId(a: T) {}
    lemma Comm(a: T, b: T) {}
    lemma MulAssoc(a: T, b: T, c: T) {}
    lemma MulLeftId(a: T) {}
    lemma MulRightId(a: T) {}
    lemma LeftDistrib(a: T, b: T, c: T) {}
    lemma RightDistrib(a: T, b: T, c: T) {}
    lemma MulZeroLeft(a: T) {}
    lemma MulZeroRight(a: T) {}
    lemma StarUnfoldLeft(a: T) {}
    lemma StarUnfoldRight(a: T) {}
}
