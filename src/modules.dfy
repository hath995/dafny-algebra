include "algebra.dfy"

// Modules and vector spaces: an abelian group of "vectors" acted on by a ring (or
// field) of "scalars". Like Subgroups/Ideals, the structure is parameterized by
// imports -- the additive group (import V) and the scalar ring (import R) -- with
// the scalar action `smul` declared abstractly. This is the conceptual parent of
// the matrix modules: an m-by-n matrix is an element of a module over its entry
// ring.

// ---- vectors used by the concrete instances ----

// The additive group Z^2 (pairs of integers, componentwise).
module IntPairGroup refines AbelianGroup {
    datatype Vec2 = V2(x: int, y: int)
    type T = Vec2
    function op(a: T, b: T): T { V2(a.x + b.x, a.y + b.y) }
    function Id(): T { V2(0, 0) }
    function Inv(a: T): T { V2(-a.x, -a.y) }

    lemma Assoc(a: T, b: T, c: T) {}
    lemma LeftId(a: T) {}
    lemma RightId(a: T) {}
    lemma LeftInv(a: T) {}
    lemma RightInv(a: T) {}
    lemma Comm(a: T, b: T) {}
}

// The additive group R^2 (pairs of reals, componentwise).
module RealPairGroup refines AbelianGroup {
    datatype Vec2 = V2(x: real, y: real)
    type T = Vec2
    function op(a: T, b: T): T { V2(a.x + b.x, a.y + b.y) }
    function Id(): T { V2(0.0, 0.0) }
    function Inv(a: T): T { V2(-a.x, -a.y) }

    lemma Assoc(a: T, b: T, c: T) {}
    lemma LeftId(a: T) {}
    lemma RightId(a: T) {}
    lemma LeftInv(a: T) {}
    lemma RightInv(a: T) {}
    lemma Comm(a: T, b: T) {}
}

// A left module over a ring R: an abelian group V with a scalar action smul
// satisfying the four module axioms below. From them, the "zero" laws and the
// behaviour of negative scalars follow -- proved once for every instantiation.
abstract module LeftModule {
    import R : Ring
    import V : AbelianGroup

    function smul(r: R.T, v: V.T): V.T

    // Scalars distribute over vector addition...
    lemma ScalarDistribVec(r: R.T, u: V.T, w: V.T)
        ensures smul(r, V.op(u, w)) == V.op(smul(r, u), smul(r, w))
    // ...and vector scaling distributes over scalar addition.
    lemma ScalarDistribScalar(r: R.T, s: R.T, v: V.T)
        ensures smul(R.op(r, s), v) == V.op(smul(r, v), smul(s, v))
    // The scalar action is associative with ring multiplication.
    lemma ScalarAssoc(r: R.T, s: R.T, v: V.T)
        ensures smul(R.mul(r, s), v) == smul(r, smul(s, v))
    // The ring identity acts trivially.
    lemma ScalarOne(v: V.T)
        ensures smul(R.One(), v) == v

    // The zero scalar sends every vector to the zero vector: 0_R . v == 0_V.
    lemma ZeroScalar(v: V.T)
        ensures smul(R.Id(), v) == V.Id()
    {
        R.LeftId(R.Id());                         // R.op(0,0) == 0
        ScalarDistribScalar(R.Id(), R.Id(), v);   // m == V.op(m, m), m := smul(0_R, v)
        var m := smul(R.Id(), v);
        V.RightId(m);                             // V.op(m, 0_V) == m
        V.LeftCancel(m, m, V.Id());               // V.op(m,m)==V.op(m,0_V) ==> m == 0_V
    }

    // Any scalar sends the zero vector to the zero vector: r . 0_V == 0_V.
    lemma ScalarZeroVec(r: R.T)
        ensures smul(r, V.Id()) == V.Id()
    {
        V.LeftId(V.Id());                         // V.op(0_V, 0_V) == 0_V
        ScalarDistribVec(r, V.Id(), V.Id());      // m == V.op(m, m), m := smul(r, 0_V)
        var m := smul(r, V.Id());
        V.RightId(m);
        V.LeftCancel(m, m, V.Id());
    }

    // A negated scalar negates the result: (-r) . v == -(r . v).
    lemma NegScalar(r: R.T, v: V.T)
        ensures smul(R.Inv(r), v) == V.Inv(smul(r, v))
    {
        ScalarDistribScalar(r, R.Inv(r), v);      // smul(op(r,-r),v) == op(smul(r,v), smul(-r,v))
        R.RightInv(r);                            // R.op(r, -r) == 0_R
        ZeroScalar(v);                            // smul(0_R, v) == 0_V
        V.InvUniqueRight(smul(r, v), smul(R.Inv(r), v));
    }
}

// Z^2 as a module over the integers, with componentwise scaling.
module ZModule refines LeftModule {
    import R = IntRing
    import V = IntPairGroup

    function smul(r: R.T, v: V.T): V.T { V.V2(r * v.x, r * v.y) }

    lemma ScalarDistribVec(r: R.T, u: V.T, w: V.T) {}
    lemma ScalarDistribScalar(r: R.T, s: R.T, v: V.T) {}
    lemma ScalarAssoc(r: R.T, s: R.T, v: V.T) {}
    lemma ScalarOne(v: V.T) {}
}

// A vector space over a field F: a left module whose scalars form a field. The
// extra structure buys cancellation by a nonzero scalar (proved below), which a
// general module lacks. Written separately from LeftModule because Dafny's single
// refinement cannot strengthen the imported scalar ring into a field.
abstract module VectorSpace {
    import F : Field
    import V : AbelianGroup

    function smul(r: F.T, v: V.T): V.T

    lemma ScalarDistribVec(r: F.T, u: V.T, w: V.T)
        ensures smul(r, V.op(u, w)) == V.op(smul(r, u), smul(r, w))
    lemma ScalarDistribScalar(r: F.T, s: F.T, v: V.T)
        ensures smul(F.op(r, s), v) == V.op(smul(r, v), smul(s, v))
    lemma ScalarAssoc(r: F.T, s: F.T, v: V.T)
        ensures smul(F.mul(r, s), v) == smul(r, smul(s, v))
    lemma ScalarOne(v: V.T)
        ensures smul(F.One(), v) == v

    // Cancel a nonzero scalar: r != 0 and r.u == r.v force u == v. (Multiply
    // through by r's inverse -- the field structure is exactly what makes this work.)
    lemma ScalarCancel(r: F.T, u: V.T, w: V.T)
        requires r != F.Id()
        requires smul(r, u) == smul(r, w)
        ensures u == w
    {
        calc {
            u;
            { ScalarOne(u); }
            smul(F.One(), u);
            { F.MulLeftInv(r); }                  // mul(r^-1, r) == 1
            smul(F.mul(F.MulInv(r), r), u);
            { ScalarAssoc(F.MulInv(r), r, u); }
            smul(F.MulInv(r), smul(r, u));
            smul(F.MulInv(r), smul(r, w));         // hypothesis smul(r,u) == smul(r,w)
            { ScalarAssoc(F.MulInv(r), r, w); }
            smul(F.mul(F.MulInv(r), r), w);
            { F.MulLeftInv(r); }
            smul(F.One(), w);
            { ScalarOne(w); }
            w;
        }
    }
}

// R^2 as a vector space over the reals, with componentwise scaling.
module R2Space refines VectorSpace {
    import F = RealField
    import V = RealPairGroup

    function smul(r: F.T, v: V.T): V.T { V.V2(r * v.x, r * v.y) }

    lemma ScalarDistribVec(r: F.T, u: V.T, w: V.T) {}
    lemma ScalarDistribScalar(r: F.T, s: F.T, v: V.T) {}
    lemma ScalarAssoc(r: F.T, s: F.T, v: V.T) {}
    lemma ScalarOne(v: V.T) {}
}
