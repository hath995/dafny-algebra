include "algebra.dfy"

// Matrices whose ELEMENT TYPE is an arbitrary commutative ring, supplied as a
// module parameter (`import R : CommRing`). Compare with matrices.dfy, where the
// element ops are abstract but have no laws — here R carries Assoc/Comm/Distrib,
// so matrix-level algebraic laws become PROVABLE rather than just assumed.
//
// Naming note from the algebra hierarchy: R.op is addition, R.Id() the additive
// zero, R.mul multiplication, R.One() the multiplicative one.
abstract module MatricesOverRing {
    import R : CommRing

    // Dot product: row i of `a` dotted with column j of `b`, first k terms.
    function Dot(a: array2<R.T>, b: array2<R.T>, i: nat, j: nat, k: nat): R.T
        requires a.Length1 == b.Length0
        requires i < a.Length0 && j < b.Length1 && k <= a.Length1
        reads a, b
        decreases k
    {
        if k == 0 then R.Id()
        else R.op(Dot(a, b, i, j, k-1), R.mul(a[i, k-1], b[k-1, j]))
    }

    method matrixAdd(a: array2<R.T>, b: array2<R.T>) returns (c: array2<R.T>)
        requires a.Length0 == b.Length0 && a.Length1 == b.Length1
        ensures fresh(c) && c.Length0 == a.Length0 && c.Length1 == a.Length1
        ensures forall i, j :: 0 <= i < c.Length0 && 0 <= j < c.Length1 ==> c[i, j] == R.op(a[i, j], b[i, j])
    {
        c := new R.T[a.Length0, a.Length1]((_, _) => R.Id());
        for i := 0 to a.Length0
            invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length1 ==> c[x, y] == R.op(a[x, y], b[x, y])
        {
            for j := 0 to a.Length1
                invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length1 ==> c[x, y] == R.op(a[x, y], b[x, y])
                invariant forall y :: 0 <= y < j ==> c[i, y] == R.op(a[i, y], b[i, y])
            {
                c[i, j] := R.op(a[i, j], b[i, j]);
            }
        }
    }

    method matrixMul(a: array2<R.T>, b: array2<R.T>) returns (c: array2<R.T>)
        requires a.Length1 == b.Length0
        ensures fresh(c) && c.Length0 == a.Length0 && c.Length1 == b.Length1
        ensures forall i, j :: 0 <= i < c.Length0 && 0 <= j < c.Length1 ==> c[i, j] == Dot(a, b, i, j, a.Length1)
    {
        c := new R.T[a.Length0, b.Length1]((_, _) => R.Id());
        for i := 0 to a.Length0
            invariant forall x, y :: 0 <= x < i && 0 <= y < b.Length1 ==> c[x, y] == Dot(a, b, x, y, a.Length1)
        {
            for j := 0 to b.Length1
                invariant forall x, y :: 0 <= x < i && 0 <= y < b.Length1 ==> c[x, y] == Dot(a, b, x, y, a.Length1)
                invariant forall y :: 0 <= y < j ==> c[i, y] == Dot(a, b, i, y, a.Length1)
            {
                c[i, j] := Dot(a, b, i, j, a.Length1);
            }
        }
    }

    // (w + x) + (y + z) == (w + y) + (x + z), purely from add associativity/commutativity.
    lemma AddRearrange4(w: R.T, x: R.T, y: R.T, z: R.T)
        ensures R.op(R.op(w, x), R.op(y, z)) == R.op(R.op(w, y), R.op(x, z))
    {
        calc {
            R.op(R.op(w, x), R.op(y, z));
            { R.Assoc(w, x, R.op(y, z)); }
            R.op(w, R.op(x, R.op(y, z)));
            { R.Assoc(x, y, z); }
            R.op(w, R.op(R.op(x, y), z));
            { R.Comm(x, y); }
            R.op(w, R.op(R.op(y, x), z));
            { R.Assoc(y, x, z); }
            R.op(w, R.op(y, R.op(x, z)));
            { R.Assoc(w, y, R.op(x, z)); }
            R.op(R.op(w, y), R.op(x, z));
        }
    }

    // The dot product distributes over an element-wise sum: if bc == b + cc, then
    // Dot(a, bc) == Dot(a, b) + Dot(a, cc). Proven from the element ring laws.
    lemma DotDistrib(a: array2<R.T>, b: array2<R.T>, cc: array2<R.T>, bc: array2<R.T>, i: nat, j: nat, k: nat)
        requires a.Length1 == b.Length0 && b.Length0 == cc.Length0 && cc.Length0 == bc.Length0
        requires b.Length1 == cc.Length1 && cc.Length1 == bc.Length1
        requires i < a.Length0 && j < b.Length1 && k <= a.Length1
        requires forall p, q :: 0 <= p < bc.Length0 && 0 <= q < bc.Length1 ==> bc[p, q] == R.op(b[p, q], cc[p, q])
        ensures Dot(a, bc, i, j, k) == R.op(Dot(a, b, i, j, k), Dot(a, cc, i, j, k))
        decreases k
    {
        if k == 0 {
            R.LeftId(R.Id());                                  // op(0, 0) == 0
        } else {
            DotDistrib(a, b, cc, bc, i, j, k-1);               // induction hypothesis
            R.LeftDistrib(a[i, k-1], b[k-1, j], cc[k-1, j]);   // a*(b+cc) == a*b + a*cc
            AddRearrange4(Dot(a, b, i, j, k-1), Dot(a, cc, i, j, k-1),
                          R.mul(a[i, k-1], b[k-1, j]), R.mul(a[i, k-1], cc[k-1, j]));
        }
    }

    // Matrix distributivity, entry-wise: (A * (B + C))[i,j] == (A*B)[i,j] + (A*C)[i,j].
    lemma MatMulDistrib(a: array2<R.T>, b: array2<R.T>, cc: array2<R.T>, bc: array2<R.T>)
        requires a.Length1 == b.Length0 && b.Length0 == cc.Length0 && cc.Length0 == bc.Length0
        requires b.Length1 == cc.Length1 && cc.Length1 == bc.Length1
        requires forall p, q :: 0 <= p < bc.Length0 && 0 <= q < bc.Length1 ==> bc[p, q] == R.op(b[p, q], cc[p, q])
        ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < b.Length1 ==>
            Dot(a, bc, i, j, a.Length1) == R.op(Dot(a, b, i, j, a.Length1), Dot(a, cc, i, j, a.Length1))
    {
        forall i, j | 0 <= i < a.Length0 && 0 <= j < b.Length1 {
            DotDistrib(a, b, cc, bc, i, j, a.Length1);
        }
    }

    // (Matrix-mul associativity and the identity law are the further laws: they
    // additionally need the swap of a double sum and zero-annihilation
    // mul(0, x) == 0, the latter derivable from RightDistrib + additive inverse.)
}

// Integer matrices, where the element ring is supplied concretely.
module IntMatricesOverRing refines MatricesOverRing {
    import R = IntRing
}
