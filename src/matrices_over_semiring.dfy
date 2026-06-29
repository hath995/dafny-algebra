include "semirings.dfy"

// Matrices whose ELEMENT TYPE is an arbitrary SEMIRING. This is the same code as
// matrices_over_ring.dfy, but with `import R : Semiring` instead of CommRing -- and
// nothing here ever uses an additive inverse or multiplicative commutativity, so
// the dot product, matrix add/mul, and distributivity all port verbatim.
//
// The point: instantiating R = Tropical turns matrix multiplication into one round
// of shortest-path relaxation (min over an intermediate node of summed edge
// weights), and that interpretation is *proved* below (DotLowerBound + DotAchieved).
//
// Naming (from the algebra hierarchy): R.op is addition, R.Id() the additive zero,
// R.mul multiplication, R.One() the multiplicative one.
abstract module MatricesOverSemiring {
    import R : Semiring

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
    // Dot(a, bc) == Dot(a, b) + Dot(a, cc). Proven from the element semiring laws.
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

    // ===================================================================
    //  Matrix multiplication is ASSOCIATIVE over any semiring.
    //
    //  Both ((AB)C)[i,j] and (A(BC))[i,j] equal the double sum
    //      sum_{k<n} sum_{l<p} a[i,k] * (b[k,l] * c[l,j]).
    //  We materialize that double sum two ways (row-major DSumRow, summing l
    //  inside k; column-major DSumCol, summing k inside l), prove they agree
    //  (Fubini), and connect each ordering to an iterated Dot via the
    //  distributive laws. The whole thing needs only the semiring axioms --
    //  crucially 0*x = x*0 = 0 (the MulZero axioms), which a ring would derive
    //  but a semiring must assume.
    // ===================================================================

    // sum_{l<lp} a[i,k] * (b[k,l] * c[l,j])  -- one row's contribution.
    function RowInner(a: array2<R.T>, b: array2<R.T>, c: array2<R.T>, i: nat, j: nat, k: nat, lp: nat): R.T
        requires a.Length1 == b.Length0 && b.Length1 == c.Length0
        requires i < a.Length0 && j < c.Length1 && k < a.Length1 && lp <= b.Length1
        reads a, b, c
        decreases lp
    {
        if lp == 0 then R.Id()
        else R.op(RowInner(a, b, c, i, j, k, lp-1), R.mul(a[i, k], R.mul(b[k, lp-1], c[lp-1, j])))
    }

    // sum_{k<kn} RowInner(k)  -- row-major double sum.
    function DSumRow(a: array2<R.T>, b: array2<R.T>, c: array2<R.T>, i: nat, j: nat, kn: nat, lp: nat): R.T
        requires a.Length1 == b.Length0 && b.Length1 == c.Length0
        requires i < a.Length0 && j < c.Length1 && kn <= a.Length1 && lp <= b.Length1
        reads a, b, c
        decreases kn
    {
        if kn == 0 then R.Id()
        else R.op(DSumRow(a, b, c, i, j, kn-1, lp), RowInner(a, b, c, i, j, kn-1, lp))
    }

    // sum_{k<kn} a[i,k] * (b[k,l] * c[l,j])  -- one column's contribution.
    function ColInner(a: array2<R.T>, b: array2<R.T>, c: array2<R.T>, i: nat, j: nat, l: nat, kn: nat): R.T
        requires a.Length1 == b.Length0 && b.Length1 == c.Length0
        requires i < a.Length0 && j < c.Length1 && l < b.Length1 && kn <= a.Length1
        reads a, b, c
        decreases kn
    {
        if kn == 0 then R.Id()
        else R.op(ColInner(a, b, c, i, j, l, kn-1), R.mul(a[i, kn-1], R.mul(b[kn-1, l], c[l, j])))
    }

    // sum_{l<lp} ColInner(l)  -- column-major double sum.
    function DSumCol(a: array2<R.T>, b: array2<R.T>, c: array2<R.T>, i: nat, j: nat, lp: nat, kn: nat): R.T
        requires a.Length1 == b.Length0 && b.Length1 == c.Length0
        requires i < a.Length0 && j < c.Length1 && lp <= b.Length1 && kn <= a.Length1
        reads a, b, c
        decreases lp
    {
        if lp == 0 then R.Id()
        else R.op(DSumCol(a, b, c, i, j, lp-1, kn), ColInner(a, b, c, i, j, lp-1, kn))
    }

    // RowInner(k) == a[i,k] * Dot(b, c, k, j, lp):  factor the constant a[i,k] out.
    lemma RowInnerIsScaledDot(a: array2<R.T>, b: array2<R.T>, c: array2<R.T>, i: nat, j: nat, k: nat, lp: nat)
        requires a.Length1 == b.Length0 && b.Length1 == c.Length0
        requires i < a.Length0 && j < c.Length1 && k < a.Length1 && lp <= b.Length1
        ensures RowInner(a, b, c, i, j, k, lp) == R.mul(a[i, k], Dot(b, c, k, j, lp))
        decreases lp
    {
        if lp == 0 {
            R.MulZeroRight(a[i, k]);                 // a[i,k]*0 == 0
        } else {
            RowInnerIsScaledDot(a, b, c, i, j, k, lp-1);
            R.LeftDistrib(a[i, k], Dot(b, c, k, j, lp-1), R.mul(b[k, lp-1], c[lp-1, j]));
        }
    }

    // ColInner(l) == Dot(a, b, i, l, kn) * c[l,j]:  factor the constant c[l,j] out.
    lemma ColInnerIsDotScaled(a: array2<R.T>, b: array2<R.T>, c: array2<R.T>, i: nat, j: nat, l: nat, kn: nat)
        requires a.Length1 == b.Length0 && b.Length1 == c.Length0
        requires i < a.Length0 && j < c.Length1 && l < b.Length1 && kn <= a.Length1
        ensures ColInner(a, b, c, i, j, l, kn) == R.mul(Dot(a, b, i, l, kn), c[l, j])
        decreases kn
    {
        if kn == 0 {
            R.MulZeroLeft(c[l, j]);                  // 0*c[l,j] == 0
        } else {
            ColInnerIsDotScaled(a, b, c, i, j, l, kn-1);
            R.RightDistrib(Dot(a, b, i, l, kn-1), R.mul(a[i, kn-1], b[kn-1, l]), c[l, j]);
            R.MulAssoc(a[i, kn-1], b[kn-1, l], c[l, j]);
        }
    }

    // Peel the outer (k) index off the column-major sum: bridges the two orderings.
    lemma DSumColPeel(a: array2<R.T>, b: array2<R.T>, c: array2<R.T>, i: nat, j: nat, lp: nat, kn: nat)
        requires a.Length1 == b.Length0 && b.Length1 == c.Length0
        requires i < a.Length0 && j < c.Length1 && lp <= b.Length1 && kn <= a.Length1
        requires kn > 0
        ensures DSumCol(a, b, c, i, j, lp, kn)
             == R.op(DSumCol(a, b, c, i, j, lp, kn-1), RowInner(a, b, c, i, j, kn-1, lp))
        decreases lp
    {
        if lp == 0 {
            R.LeftId(R.Id());
        } else {
            DSumColPeel(a, b, c, i, j, lp-1, kn);
            AddRearrange4(DSumCol(a, b, c, i, j, lp-1, kn-1), RowInner(a, b, c, i, j, kn-1, lp-1),
                          ColInner(a, b, c, i, j, lp-1, kn-1),
                          R.mul(a[i, kn-1], R.mul(b[kn-1, lp-1], c[lp-1, j])));
        }
    }

    // Empty outer index: the column-major sum over zero k's is 0.
    lemma DSumColZero(a: array2<R.T>, b: array2<R.T>, c: array2<R.T>, i: nat, j: nat, lp: nat)
        requires a.Length1 == b.Length0 && b.Length1 == c.Length0
        requires i < a.Length0 && j < c.Length1 && lp <= b.Length1
        ensures DSumCol(a, b, c, i, j, lp, 0) == R.Id()
        decreases lp
    {
        if lp != 0 {
            DSumColZero(a, b, c, i, j, lp-1);
            R.RightId(R.Id());
        }
    }

    // FUBINI: the two summation orders agree.
    lemma Fubini(a: array2<R.T>, b: array2<R.T>, c: array2<R.T>, i: nat, j: nat, kn: nat, lp: nat)
        requires a.Length1 == b.Length0 && b.Length1 == c.Length0
        requires i < a.Length0 && j < c.Length1 && kn <= a.Length1 && lp <= b.Length1
        ensures DSumRow(a, b, c, i, j, kn, lp) == DSumCol(a, b, c, i, j, lp, kn)
        decreases kn
    {
        if kn == 0 {
            DSumColZero(a, b, c, i, j, lp);
        } else {
            Fubini(a, b, c, i, j, kn-1, lp);
            DSumColPeel(a, b, c, i, j, lp, kn);
        }
    }

    // (AB)C entry == column-major double sum, given ab == A*B.
    lemma DotAbIsDSumCol(a: array2<R.T>, b: array2<R.T>, c: array2<R.T>, ab: array2<R.T>, i: nat, j: nat, lp: nat)
        requires a.Length1 == b.Length0 && b.Length1 == c.Length0
        requires ab.Length0 == a.Length0 && ab.Length1 == b.Length1
        requires forall x, y :: 0 <= x < ab.Length0 && 0 <= y < ab.Length1 ==> ab[x, y] == Dot(a, b, x, y, a.Length1)
        requires i < a.Length0 && j < c.Length1 && lp <= b.Length1
        ensures Dot(ab, c, i, j, lp) == DSumCol(a, b, c, i, j, lp, a.Length1)
        decreases lp
    {
        if lp != 0 {
            DotAbIsDSumCol(a, b, c, ab, i, j, lp-1);
            ColInnerIsDotScaled(a, b, c, i, j, lp-1, a.Length1);
        }
    }

    // A(BC) entry == row-major double sum, given bc == B*C.
    lemma DotBcIsDSumRow(a: array2<R.T>, b: array2<R.T>, c: array2<R.T>, bc: array2<R.T>, i: nat, j: nat, kn: nat)
        requires a.Length1 == b.Length0 && b.Length1 == c.Length0
        requires bc.Length0 == b.Length0 && bc.Length1 == c.Length1
        requires forall x, y :: 0 <= x < bc.Length0 && 0 <= y < bc.Length1 ==> bc[x, y] == Dot(b, c, x, y, b.Length1)
        requires i < a.Length0 && j < c.Length1 && kn <= a.Length1
        ensures Dot(a, bc, i, j, kn) == DSumRow(a, b, c, i, j, kn, b.Length1)
        decreases kn
    {
        if kn != 0 {
            DotBcIsDSumRow(a, b, c, bc, i, j, kn-1);
            RowInnerIsScaledDot(a, b, c, i, j, kn-1, b.Length1);
        }
    }

    // The payoff: (AB)C == A(BC), entry by entry, for matrices over any semiring.
    lemma MatMulAssoc(a: array2<R.T>, b: array2<R.T>, c: array2<R.T>, ab: array2<R.T>, bc: array2<R.T>, i: nat, j: nat)
        requires a.Length1 == b.Length0 && b.Length1 == c.Length0
        requires ab.Length0 == a.Length0 && ab.Length1 == b.Length1
        requires bc.Length0 == b.Length0 && bc.Length1 == c.Length1
        requires forall x, y :: 0 <= x < ab.Length0 && 0 <= y < ab.Length1 ==> ab[x, y] == Dot(a, b, x, y, a.Length1)
        requires forall x, y :: 0 <= x < bc.Length0 && 0 <= y < bc.Length1 ==> bc[x, y] == Dot(b, c, x, y, b.Length1)
        requires i < a.Length0 && j < c.Length1
        ensures Dot(ab, c, i, j, ab.Length1) == Dot(a, bc, i, j, a.Length1)
    {
        DotAbIsDSumCol(a, b, c, ab, i, j, ab.Length1);     // (AB)C == DSumCol
        Fubini(a, b, c, i, j, a.Length1, b.Length1);        // DSumRow == DSumCol
        DotBcIsDSumRow(a, b, c, bc, i, j, a.Length1);       // A(BC) == DSumRow
    }

    // ===================================================================
    //  Purely functional matrices: a matrix is just a total index function
    //  (nat,nat) -> R.T. Heap-free and immutable, so it inducts cleanly --
    //  this is the right substrate for the walk/shortest-path theorem (over
    //  GPow). The array `Dot`/`matrixMul` are then proved EQUIVALENT to this
    //  functional view, so the executable code and the functional spec agree.
    // ===================================================================

    // Functional dot product: first k terms of row i of f against column j of g.
    function GDot(f: (nat, nat) -> R.T, g: (nat, nat) -> R.T, i: nat, j: nat, k: nat): R.T
        decreases k
    {
        if k == 0 then R.Id()
        else R.op(GDot(f, g, i, j, k-1), R.mul(f(i, k-1), g(k-1, j)))
    }

    // Functional product / identity / power (n = shared inner dimension).
    function GMul(n: nat, f: (nat, nat) -> R.T, g: (nat, nat) -> R.T): (nat, nat) -> R.T
    {
        (i: nat, j: nat) => GDot(f, g, i, j, n)
    }
    function GId(): (nat, nat) -> R.T
    {
        (i: nat, j: nat) => if i == j then R.One() else R.Id()
    }
    function GPow(n: nat, f: (nat, nat) -> R.T, p: nat): (nat, nat) -> R.T
        decreases p
    {
        if p == 0 then GId() else GMul(n, f, GPow(n, f, p-1))
    }

    // Applying the functional product is just GDot (unfold the lambda).
    lemma GMulApply(n: nat, f: (nat, nat) -> R.T, g: (nat, nat) -> R.T, i: nat, j: nat)
        ensures GMul(n, f, g)(i, j) == GDot(f, g, i, j, n)
    {
    }

    // EQUIVALENCE: the array dot product agrees with the functional one, for any
    // index functions that read back the arrays on their valid ranges.
    lemma DotEqGDot(arrA: array2<R.T>, arrB: array2<R.T>, f: (nat, nat) -> R.T, g: (nat, nat) -> R.T, i: nat, j: nat, k: nat)
        requires arrA.Length1 == arrB.Length0
        requires i < arrA.Length0 && j < arrB.Length1 && k <= arrA.Length1
        requires forall x, y :: 0 <= x < arrA.Length0 && 0 <= y < arrA.Length1 ==> f(x, y) == arrA[x, y]
        requires forall x, y :: 0 <= x < arrB.Length0 && 0 <= y < arrB.Length1 ==> g(x, y) == arrB[x, y]
        ensures Dot(arrA, arrB, i, j, k) == GDot(f, g, i, j, k)
        decreases k
    {
        if k != 0 {
            DotEqGDot(arrA, arrB, f, g, i, j, k-1);
        }
    }

    // ...lifting to whole matrices: matrixMul's output IS the functional product.
    lemma MatMulIsGMul(arrA: array2<R.T>, arrB: array2<R.T>, f: (nat, nat) -> R.T, g: (nat, nat) -> R.T, c: array2<R.T>, i: nat, j: nat)
        requires arrA.Length1 == arrB.Length0
        requires c.Length0 == arrA.Length0 && c.Length1 == arrB.Length1
        requires forall x, y :: 0 <= x < c.Length0 && 0 <= y < c.Length1 ==> c[x, y] == Dot(arrA, arrB, x, y, arrA.Length1)
        requires forall x, y :: 0 <= x < arrA.Length0 && 0 <= y < arrA.Length1 ==> f(x, y) == arrA[x, y]
        requires forall x, y :: 0 <= x < arrB.Length0 && 0 <= y < arrB.Length1 ==> g(x, y) == arrB[x, y]
        requires i < c.Length0 && j < c.Length1
        ensures c[i, j] == GMul(arrA.Length1, f, g)(i, j)
    {
        DotEqGDot(arrA, arrB, f, g, i, j, arrA.Length1);
        GMulApply(arrA.Length1, f, g, i, j);
    }

    // ---- walks, for the shortest-path theorem (positive powers Pow1 = f^p) ----

    // f^p for p >= 1 (base f, not the identity -- avoids identity-matrix edge cases).
    function Pow1(n: nat, f: (nat, nat) -> R.T, p: nat): (nat, nat) -> R.T
        requires p >= 1
        decreases p
    {
        if p == 1 then f else GMul(n, f, Pow1(n, f, p-1))
    }

    // A length-p walk i = v0, v1, ..., vp = j with all vertices in [0, n).
    ghost predicate IsWalk(walk: seq<nat>, i: nat, j: nat, p: nat, n: nat) {
        && |walk| == p + 1
        && walk[0] == i
        && walk[|walk|-1] == j
        && forall t :: 0 <= t < |walk| ==> walk[t] < n
    }

    // Weight of a walk: the semiring product of its edge weights (tropically, the
    // sum of the edge costs). Peels the first edge to match Pow1's left recursion.
    function WalkWeight(f: (nat, nat) -> R.T, walk: seq<nat>): R.T
        requires |walk| >= 1
        decreases |walk|
    {
        if |walk| == 1 then R.One()
        else R.mul(f(walk[0], walk[1]), WalkWeight(f, walk[1..]))
    }
}

// Matrices over the naturals: the semiring port works for an ordinary (non-ordered)
// semiring too.
module NatMatrices refines MatricesOverSemiring {
    import R = NatSemiring
}

// Matrices over the tropical (min,+) semiring. Here a matrix product IS one round of
// shortest-path relaxation: c[i,j] = min over an intermediate node m of a[i,m]+b[m,j].
// We prove exactly that -- Dot is a lower bound on every single-intermediate weight,
// and it equals the weight through some specific intermediate node -- so it is their
// minimum. Iterating (powers of an adjacency matrix) is then Floyd-Warshall.
module TropicalMatrices refines MatricesOverSemiring {
    import R = Tropical

    // x <= y in the tropical order (x is "no farther than" y).
    ghost predicate TLeq(x: R.T, y: R.T) { R.op(x, y) == x }

    // SOUNDNESS: the (i,j) product is <= the weight through every intermediate m,
    // i.e. it never overestimates a real path.
    lemma DotLowerBound(a: array2<R.T>, b: array2<R.T>, i: nat, j: nat, k: nat, m: nat)
        requires a.Length1 == b.Length0
        requires i < a.Length0 && j < b.Length1 && k <= a.Length1
        requires 0 <= m < k
        ensures TLeq(Dot(a, b, i, j, k), R.mul(a[i, m], b[m, j]))
        decreases k
    {
        var prev := Dot(a, b, i, j, k-1);
        var last := R.mul(a[i, k-1], b[k-1, j]);
        var d := R.op(prev, last);                 // == Dot(a,b,i,j,k)
        if m == k - 1 {
            R.LeqRight(prev, last);                 // d <= last == a[i,m]*b[m,j]
        } else {
            DotLowerBound(a, b, i, j, k-1, m);      // prev <= a[i,m]*b[m,j]
            R.LeqLeft(prev, last);                  // d <= prev
            R.LeqTrans(d, prev, R.mul(a[i, m], b[m, j]));
        }
    }

    // TIGHTNESS: the product is ACHIEVED by some intermediate node m -- so together
    // with DotLowerBound it equals the minimum single-intermediate path weight.
    lemma DotAchieved(a: array2<R.T>, b: array2<R.T>, i: nat, j: nat, k: nat) returns (m: nat)
        requires a.Length1 == b.Length0
        requires i < a.Length0 && j < b.Length1 && k <= a.Length1
        requires k > 0
        ensures 0 <= m < k && Dot(a, b, i, j, k) == R.mul(a[i, m], b[m, j])
        decreases k
    {
        var prev := Dot(a, b, i, j, k-1);
        var last := R.mul(a[i, k-1], b[k-1, j]);
        R.OpPicks(prev, last);                      // op(prev,last) is prev or last
        if R.op(prev, last) == last {
            m := k - 1;
        } else {
            // op picked prev, so Dot == prev. prev can't be the empty product Id here:
            // op(Id, last) == last would force the other branch.
            if k - 1 == 0 {
                R.LeftId(last);
                assert false;
            }
            m := DotAchieved(a, b, i, j, k-1);
        }
    }

    // ---- functional versions of the relaxation facts (no arrays, for induction) ----

    lemma GDotLowerBound(f: (nat, nat) -> R.T, g: (nat, nat) -> R.T, i: nat, j: nat, k: nat, m: nat)
        requires 0 <= m < k
        ensures TLeq(GDot(f, g, i, j, k), R.mul(f(i, m), g(m, j)))
        decreases k
    {
        var prev := GDot(f, g, i, j, k-1);
        var last := R.mul(f(i, k-1), g(k-1, j));
        if m == k - 1 {
            R.LeqRight(prev, last);
        } else {
            GDotLowerBound(f, g, i, j, k-1, m);
            R.LeqLeft(prev, last);
            R.LeqTrans(R.op(prev, last), prev, R.mul(f(i, m), g(m, j)));
        }
    }

    lemma GDotAchieved(f: (nat, nat) -> R.T, g: (nat, nat) -> R.T, i: nat, j: nat, k: nat) returns (m: nat)
        requires k > 0
        ensures 0 <= m < k && GDot(f, g, i, j, k) == R.mul(f(i, m), g(m, j))
        decreases k
    {
        var prev := GDot(f, g, i, j, k-1);
        var last := R.mul(f(i, k-1), g(k-1, j));
        R.OpPicks(prev, last);
        if R.op(prev, last) == last {
            m := k - 1;
        } else {
            if k - 1 == 0 {
                R.LeftId(last);
                assert false;
            }
            m := GDotAchieved(f, g, i, j, k-1);
        }
    }

    // ===================================================================
    //  SHORTEST PATHS. Over the tropical semiring, the (i,j) entry of the p-th
    //  power of the (functional) adjacency matrix equals the minimum weight of
    //  any length-p walk from i to j: it is <= every walk (WalkSound) and is
    //  ACHIEVED by some walk (WalkTight). Via MatMulIsGMul this carries onto the
    //  executable array matrixMul -- a fully verified Floyd-Warshall core.
    // ===================================================================

    // Soundness: the matrix power never overestimates a real walk.
    lemma WalkSound(f: (nat, nat) -> R.T, walk: seq<nat>, i: nat, j: nat, p: nat, n: nat)
        requires p >= 1
        requires IsWalk(walk, i, j, p, n)
        ensures TLeq(Pow1(n, f, p)(i, j), WalkWeight(f, walk))
        decreases p
    {
        if p == 1 {
            R.MulRightId(f(i, j));     // WalkWeight([i,j]) == f(i,j) == Pow1(1)(i,j)
            R.OpIdem(f(i, j));         // <= is reflexive
        } else {
            var g := Pow1(n, f, p-1);
            var k := walk[1];
            assert walk[0] == i && k < n;
            GMulApply(n, f, g, i, j);                     // Pow1(p)(i,j) == GDot(f,g,i,j,n)
            GDotLowerBound(f, g, i, j, n, k);             // <= mul(f(i,k), g(k,j))
            WalkSound(f, walk[1..], k, j, p-1, n);        // g(k,j) <= WalkWeight(walk[1..])
            R.MulMono(f(i, k), g(k, j), WalkWeight(f, walk[1..]));
            R.LeqTrans(Pow1(n, f, p)(i, j), R.mul(f(i, k), g(k, j)), WalkWeight(f, walk));
        }
    }

    // Tightness: the matrix power is the weight of some actual walk.
    lemma WalkTight(f: (nat, nat) -> R.T, i: nat, j: nat, p: nat, n: nat) returns (walk: seq<nat>)
        requires p >= 1 && i < n && j < n
        ensures IsWalk(walk, i, j, p, n)
        ensures Pow1(n, f, p)(i, j) == WalkWeight(f, walk)
        decreases p
    {
        if p == 1 {
            walk := [i, j];
            R.MulRightId(f(i, j));
        } else {
            var g := Pow1(n, f, p-1);
            GMulApply(n, f, g, i, j);                     // Pow1(p)(i,j) == GDot(f,g,i,j,n)
            var m := GDotAchieved(f, g, i, j, n);         // == mul(f(i,m), g(m,j)), m < n
            var w := WalkTight(f, m, j, p-1, n);          // g(m,j) == WalkWeight(w), IsWalk(w,m,j,p-1,n)
            walk := [i] + w;
            assert walk[1..] == w && walk[1] == m;        // [i]+w : index 1 is w[0] == m
        }
    }

    // ===================================================================
    //  FLOYD-WARSHALL. The (i,j) shortest distance using only intermediate
    //  vertices < k, defined by the FW recurrence itself:
    //      SV(i,j,0)   = w(i,j)                                  (direct edge)
    //      SV(i,j,k+1) = min( SV(i,j,k),  SV(i,k,k) + SV(k,j,k) )
    //  The in-place triple loop below is proved to compute SV(.,.,n).
    // ===================================================================
    // Opaque so the big FW loop invariants treat it as an uninterpreted function
    // (no recursive unfolding across the quantifiers); we reveal it only in the
    // small lemmas below, where exactly one unfolding step is needed.
    opaque function ShortestVia(w: (nat, nat) -> R.T, i: nat, j: nat, k: nat): R.T
        decreases k
    {
        if k == 0 then w(i, j)
        else R.op(ShortestVia(w, i, j, k-1),
                  R.mul(ShortestVia(w, i, k-1, k-1), ShortestVia(w, k-1, j, k-1)))
    }

    // Base: with no intermediates, the distance is the direct edge.
    lemma SVBase(w: (nat, nat) -> R.T, i: nat, j: nat)
        ensures ShortestVia(w, i, j, 0) == w(i, j)
    {
        reveal ShortestVia();
    }

    // One unfolding of the FW recurrence.
    lemma SVStep(w: (nat, nat) -> R.T, i: nat, j: nat, k: nat)
        ensures ShortestVia(w, i, j, k+1)
             == R.op(ShortestVia(w, i, j, k), R.mul(ShortestVia(w, i, k, k), ShortestVia(w, k, j, k)))
    {
        reveal ShortestVia();
    }

    // Floyd-Warshall over the tropical semiring. Each round writes D^(k+1) into a
    // FRESH array, read from the previous round D^(k): every entry is exactly the FW
    // recurrence applied to the previous matrix, so there is no in-place aliasing to
    // reason about (and no "no improving cycles" precondition is needed). Input `a`
    // is the edge-weight matrix; output `d` is the closure SV(.,.,n).
    method FloydWarshall(a: array2<R.T>, ghost w: (nat, nat) -> R.T, n: nat) returns (d: array2<R.T>)
        requires a.Length0 == n && a.Length1 == n
        requires forall i, j :: 0 <= i < n && 0 <= j < n ==> a[i, j] == w(i, j)
        ensures d.Length0 == n && d.Length1 == n
        ensures forall i, j :: 0 <= i < n && 0 <= j < n ==> d[i, j] == ShortestVia(w, i, j, n)
    {
        // D^(0) = a (the edge matrix), so cur[i,j] == w(i,j) == SV(i,j,0).
        var cur := new R.T[n, n]((i, j) reads a =>
            if 0 <= i < a.Length0 && 0 <= j < a.Length1 then a[i, j] else R.Id());
        forall i, j | 0 <= i < n && 0 <= j < n
            ensures cur[i, j] == ShortestVia(w, i, j, 0)
        {
            SVBase(w, i, j);
        }
        for k := 0 to n
            invariant cur.Length0 == n && cur.Length1 == n
            invariant forall i, j :: 0 <= i < n && 0 <= j < n ==> cur[i, j] == ShortestVia(w, i, j, k)
        {
            // D^(k+1)[i,j] = min( D^(k)[i,j], D^(k)[i,k] + D^(k)[k,j] ).
            var next := new R.T[n, n]((i, j) reads cur =>
                if 0 <= i < cur.Length0 && 0 <= j < cur.Length1 && k < cur.Length0 && k < cur.Length1
                then R.op(cur[i, j], R.mul(cur[i, k], cur[k, j]))
                else R.Id());
            forall i, j | 0 <= i < n && 0 <= j < n
                ensures next[i, j] == ShortestVia(w, i, j, k+1)
            {
                SVStep(w, i, j, k);   // SV(i,j,k+1) == op(SV(i,j,k), mul(SV(i,k,k), SV(k,j,k)))
            }
            cur := next;
        }
        d := cur;
    }
}
