// Abstract matrix arithmetic over a commutative-ring-like element type.
//
// The element type T and its Zero/One/Add/Mul are abstract, so a refinement only
// has to supply those (as with the Medians abstract module). Add/Mul must be
// TOTAL — which is why nat/int/real fit but bounded types like nint64 do not
// (their + and * can overflow the newtype). Subtraction lives in the richer
// RingMatrices refinement, since it needs an additive inverse (so nat opts out).
abstract module Matrices {
    type T(==, !new)

    function Zero(): T
    function One(): T
    function Add(a: T, b: T): T
    function Mul(a: T, b: T): T

    // ---- dot product: row i of `a` dotted with column j of `b`, first k terms ----
    function Dot(a: array2<T>, b: array2<T>, i: nat, j: nat, k: nat): T
        requires a.Length1 == b.Length0
        requires i < a.Length0 && j < b.Length1 && k <= a.Length1
        reads a, b
        decreases k
    {
        if k == 0 then Zero()
        else Add(Dot(a, b, i, j, k-1), Mul(a[i, k-1], b[k-1, j]))
    } by method {
        var acc := Zero();
        for l := 0 to k
            invariant acc == Dot(a, b, i, j, l)
        {
            acc := Add(acc, Mul(a[i, l], b[l, j]));
        }
        return acc;
    }

    method matrixAdd(a: array2<T>, b: array2<T>) returns (c: array2<T>)
        requires a.Length0 == b.Length0 && a.Length1 == b.Length1
        ensures fresh(c)
        ensures c.Length0 == a.Length0 && c.Length1 == a.Length1
        ensures forall i, j :: 0 <= i < c.Length0 && 0 <= j < c.Length1 ==> c[i, j] == Add(a[i, j], b[i, j])
    {
        c := new T[a.Length0, a.Length1]((_, _) => Zero());
        for i := 0 to a.Length0
            invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length1 ==> c[x, y] == Add(a[x, y], b[x, y])
        {
            for j := 0 to a.Length1
                invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length1 ==> c[x, y] == Add(a[x, y], b[x, y])
                invariant forall y :: 0 <= y < j ==> c[i, y] == Add(a[i, y], b[i, y])
            {
                c[i, j] := Add(a[i, j], b[i, j]);
            }
        }
    }

    method matrixMul(a: array2<T>, b: array2<T>) returns (c: array2<T>)
        requires a.Length1 == b.Length0
        ensures fresh(c)
        ensures c.Length0 == a.Length0 && c.Length1 == b.Length1
        ensures forall i, j :: 0 <= i < c.Length0 && 0 <= j < c.Length1 ==> c[i, j] == Dot(a, b, i, j, a.Length1)
    {
        c := new T[a.Length0, b.Length1]((_, _) => Zero());
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

    // ---- transpose ----
    method transpose(a: array2<T>) returns (c: array2<T>)
        ensures fresh(c)
        ensures c.Length0 == a.Length1 && c.Length1 == a.Length0
        ensures forall i, j :: 0 <= i < c.Length0 && 0 <= j < c.Length1 ==> c[i, j] == a[j, i]
    {
        c := new T[a.Length1, a.Length0]((_, _) => Zero());
        for i := 0 to a.Length1
            invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length0 ==> c[x, y] == a[y, x]
        {
            for j := 0 to a.Length0
                invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length0 ==> c[x, y] == a[y, x]
                invariant forall y :: 0 <= y < j ==> c[i, y] == a[y, i]
            {
                c[i, j] := a[j, i];
            }
        }
    }

    // ---- scalar multiply ----
    method scalarMul(s: T, a: array2<T>) returns (c: array2<T>)
        ensures fresh(c)
        ensures c.Length0 == a.Length0 && c.Length1 == a.Length1
        ensures forall i, j :: 0 <= i < c.Length0 && 0 <= j < c.Length1 ==> c[i, j] == Mul(s, a[i, j])
    {
        c := new T[a.Length0, a.Length1]((_, _) => Zero());
        for i := 0 to a.Length0
            invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length1 ==> c[x, y] == Mul(s, a[x, y])
        {
            for j := 0 to a.Length1
                invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length1 ==> c[x, y] == Mul(s, a[x, y])
                invariant forall y :: 0 <= y < j ==> c[i, y] == Mul(s, a[i, y])
            {
                c[i, j] := Mul(s, a[i, j]);
            }
        }
    }

    // ---- Hadamard (element-wise) product ----
    method hadamard(a: array2<T>, b: array2<T>) returns (c: array2<T>)
        requires a.Length0 == b.Length0 && a.Length1 == b.Length1
        ensures fresh(c)
        ensures c.Length0 == a.Length0 && c.Length1 == a.Length1
        ensures forall i, j :: 0 <= i < c.Length0 && 0 <= j < c.Length1 ==> c[i, j] == Mul(a[i, j], b[i, j])
    {
        c := new T[a.Length0, a.Length1]((_, _) => Zero());
        for i := 0 to a.Length0
            invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length1 ==> c[x, y] == Mul(a[x, y], b[x, y])
        {
            for j := 0 to a.Length1
                invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length1 ==> c[x, y] == Mul(a[x, y], b[x, y])
                invariant forall y :: 0 <= y < j ==> c[i, y] == Mul(a[i, y], b[i, y])
            {
                c[i, j] := Mul(a[i, j], b[i, j]);
            }
        }
    }

    // ---- trace (sum of the diagonal of a square matrix) ----
    function DiagSum(a: array2<T>, k: nat): T
        requires a.Length0 == a.Length1 && k <= a.Length0
        reads a
        decreases k
    {
        if k == 0 then Zero() else Add(DiagSum(a, k-1), a[k-1, k-1])
    }

    method trace(a: array2<T>) returns (t: T)
        requires a.Length0 == a.Length1
        ensures t == DiagSum(a, a.Length0)
    {
        t := Zero();
        for i := 0 to a.Length0
            invariant t == DiagSum(a, i)
        {
            t := Add(t, a[i, i]);
        }
    }

    // ---- identity ----
    method identity(n: nat) returns (c: array2<T>)
        ensures fresh(c)
        ensures c.Length0 == n && c.Length1 == n
        ensures forall i, j :: 0 <= i < n && 0 <= j < n ==> c[i, j] == (if i == j then One() else Zero())
    {
        c := new T[n, n]((i, j) => if i == j then One() else Zero());
    }

    // ---- matrix power (square), a^n = a * a^(n-1), a^0 = I ----
    // Functional spec of the (i,j) entry of a^n, so `pow` is provably the power.
    ghost function MatPowEntry(a: array2<T>, n: nat, i: nat, j: nat): T
        requires a.Length0 == a.Length1 && i < a.Length0 && j < a.Length0
        reads a
        decreases n, 1, 0
    {
        if n == 0 then (if i == j then One() else Zero())
        else PowDot(a, n, i, j, a.Length0)
    }

    ghost function PowDot(a: array2<T>, n: nat, i: nat, j: nat, k: nat): T
        requires a.Length0 == a.Length1 && n >= 1 && i < a.Length0 && j < a.Length0 && k <= a.Length0
        reads a
        decreases n, 0, k
    {
        if k == 0 then Zero()
        else Add(PowDot(a, n, i, j, k-1), Mul(a[i, k-1], MatPowEntry(a, n-1, k-1, j)))
    }

    // One step of `pow`: matrixMul against a^(n-1) computes the n-th power's entry.
    lemma DotEqPowDot(a: array2<T>, prev: array2<T>, n: nat, i: nat, j: nat, k: nat)
        requires a.Length0 == a.Length1 && n >= 1
        requires prev.Length0 == a.Length0 && prev.Length1 == a.Length0
        requires i < a.Length0 && j < a.Length0 && k <= a.Length0
        requires forall l :: 0 <= l < a.Length0 ==> prev[l, j] == MatPowEntry(a, n-1, l, j)
        ensures Dot(a, prev, i, j, k) == PowDot(a, n, i, j, k)
        decreases k
    {
        if k > 0 {
            DotEqPowDot(a, prev, n, i, j, k-1);
        }
    }

    method pow(a: array2<T>, n: nat) returns (c: array2<T>)
        requires a.Length0 == a.Length1
        ensures fresh(c)
        ensures c.Length0 == a.Length0 && c.Length1 == a.Length0
        ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length0 ==> c[i, j] == MatPowEntry(a, n, i, j)
        decreases n
    {
        if n == 0 {
            c := identity(a.Length0);
        } else {
            var prev := pow(a, n-1);
            c := matrixMul(a, prev);
            forall i, j | 0 <= i < a.Length0 && 0 <= j < a.Length0
                ensures c[i, j] == MatPowEntry(a, n, i, j)
            {
                DotEqPowDot(a, prev, n, i, j, a.Length0);
            }
        }
    }
}

module NatMatrices1 refines Matrices {
    type T = nat
    function Zero(): T { 0 }
    function One(): T { 1 }
    function Add(a: T, b: T): T { a + b }
    function Mul(a: T, b: T): T { a * b }
}

// Adds subtraction, which needs an additive inverse — so nat cannot refine this,
// only types that have negation (int, real, ...).
abstract module RingMatrices refines Matrices {
    function Neg(a: T): T
    function Sub(a: T, b: T): T { Add(a, Neg(b)) }

    method matrixSub(a: array2<T>, b: array2<T>) returns (c: array2<T>)
        requires a.Length0 == b.Length0 && a.Length1 == b.Length1
        ensures fresh(c)
        ensures c.Length0 == a.Length0 && c.Length1 == a.Length1
        ensures forall i, j :: 0 <= i < c.Length0 && 0 <= j < c.Length1 ==> c[i, j] == Sub(a[i, j], b[i, j])
    {
        c := new T[a.Length0, a.Length1]((_, _) => Zero());
        for i := 0 to a.Length0
            invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length1 ==> c[x, y] == Sub(a[x, y], b[x, y])
        {
            for j := 0 to a.Length1
                invariant forall x, y :: 0 <= x < i && 0 <= y < a.Length1 ==> c[x, y] == Sub(a[x, y], b[x, y])
                invariant forall y :: 0 <= y < j ==> c[i, y] == Sub(a[i, y], b[i, y])
            {
                c[i, j] := Sub(a[i, j], b[i, j]);
            }
        }
    }
}

module IntMatrices refines RingMatrices {
    type T = int
    function Zero(): T { 0 }
    function One(): T { 1 }
    function Add(a: T, b: T): T { a + b }
    function Mul(a: T, b: T): T { a * b }
    function Neg(a: T): T { -a }
}

module RealMatrices refines RingMatrices {
    type T = real
    function Zero(): T { 0.0 }
    function One(): T { 1.0 }
    function Add(a: T, b: T): T { a + b }
    function Mul(a: T, b: T): T { a * b }
    function Neg(a: T): T { -a }
}
