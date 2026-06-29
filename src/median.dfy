abstract module Medians {
    import opened Std.Relations
    import opened Std.Collections.Seq
    type T(==,!new)

    predicate Lte(a: T, b: T)

    function add(a: T, b: T): T
    function halve(a: T): T

    function Median(xs: seq<T>): T
        requires TotalOrdering(Lte)
        requires |xs| > 0
    {
        var ss := MergeSortBy(Lte, xs);
        if |ss| % 2 == 0 then halve(add(ss[|ss|/2 - 1], ss[|ss|/2])) else ss[|ss|/2]
    }

    // A median splits the (sorted) data: everything up to the middle is Lte it,
    // and everything from the middle on is Gte it. For odd length the Median is
    // exactly the middle order statistic, so this holds with no assumptions
    // beyond Lte being a total ordering.
    lemma MedianSplitsOdd(xs: seq<T>)
        requires TotalOrdering(Lte)
        requires |xs| > 0 && |xs| % 2 == 1
        ensures var ss := MergeSortBy(Lte, xs);
            && Median(xs) == ss[|xs|/2]
            && (forall i :: 0 <= i <= |xs|/2 ==> Lte(ss[i], Median(xs)))     // lower half (and middle) <= median
            && (forall i :: |xs|/2 <= i < |xs| ==> Lte(Median(xs), ss[i]))   // middle (and upper half) >= median
    {
        var ss := MergeSortBy(Lte, xs);          // SortedBy(Lte, ss), multiset(ss) == multiset(xs)
        assert Reflexive(Lte);                   // from TotalOrdering, so Lte(ss[mid], ss[mid])
    }

    // The claim about the *original* (unsorted) data: at least half of xs is Lte
    // the median, and at least half is Gte it — the rank/balance definition. The
    // witnesses are the lower/upper halves of the sorted data, sub-multisets of
    // xs because multiset(ss) == multiset(xs).
    lemma MedianBalanceOdd(xs: seq<T>)
        requires TotalOrdering(Lte)
        requires |xs| > 0 && |xs| % 2 == 1
        ensures exists lo :: lo <= multiset(xs) && |lo| == (|xs|+1)/2 && (forall e :: e in lo ==> Lte(e, Median(xs)))
        ensures exists hi :: hi <= multiset(xs) && |hi| == (|xs|+1)/2 && (forall e :: e in hi ==> Lte(Median(xs), e))
    {
        var ss := MergeSortBy(Lte, xs);
        var mid := |xs| / 2;
        assert Median(xs) == ss[mid];
        assert SortedBy(Lte, ss);
        assert Reflexive(Lte);
        assert |ss| == |xs|;

        var lo := multiset(ss[..mid+1]);
        assert ss[..mid+1] + ss[mid+1..] == ss;
        assert multiset(xs) == lo + multiset(ss[mid+1..]);      // lo <= multiset(xs)
        forall e | e in lo ensures Lte(e, Median(xs)) {
            var k :| 0 <= k < mid+1 && ss[..mid+1][k] == e;     // e is some ss[k], k <= mid
            assert ss[k] == e;
        }

        var hi := multiset(ss[mid..]);
        assert ss[..mid] + ss[mid..] == ss;
        assert multiset(xs) == multiset(ss[..mid]) + hi;        // hi <= multiset(xs)
        forall e | e in hi ensures Lte(Median(xs), e) {
            var k :| 0 <= k < |ss[mid..]| && ss[mid..][k] == e; // e is some ss[mid+k], mid+k >= mid
            assert ss[mid + k] == e;
        }
    }

    // For even length the Median is the average of the two central order
    // statistics, which is a median provided averaging stays between its inputs
    // (true for int/real; fails for bv8 on overflow). That property is taken as
    // a hypothesis here and discharged by the concrete refinements below.
    lemma MedianSplitsEven(xs: seq<T>)
        requires TotalOrdering(Lte)
        requires |xs| > 0 && |xs| % 2 == 0
        requires forall a, b :: Lte(a, b) ==> Lte(a, halve(add(a, b))) && Lte(halve(add(a, b)), b)
        ensures var ss := MergeSortBy(Lte, xs);
            && Median(xs) == halve(add(ss[|xs|/2 - 1], ss[|xs|/2]))
            && Lte(ss[|xs|/2 - 1], Median(xs))    // lower central <= median
            && Lte(Median(xs), ss[|xs|/2])        // median <= upper central
    {
        var ss := MergeSortBy(Lte, xs);
        assert |ss| == |xs|;
        assert SortedBy(Lte, ss);                 // so Lte(ss[mid-1], ss[mid]) for the two centrals
    }
}

module IntMedian refines Medians {
    type T = int

    function add(a: T, b: T):T {
        a+b
    }

    function halve(a: T):T {
        a / 2
    }

    predicate Lte(a: T, b:T ) {
        a <= b
    }

    // Integer (floor) averaging stays between its inputs, so the even-length
    // median is a genuine median.
    lemma Averaging()
        ensures forall a: T, b: T :: Lte(a, b) ==> Lte(a, halve(add(a, b))) && Lte(halve(add(a, b)), b)
    {}
}

module BvMedian refines Medians {
    type T = bv8

    function add(a: T, b: T):T {
        a+b
    }

    function halve(a: T):T {
        a >> 1
    }

    predicate Lte(a: T, b:T ) {
        a <= b
    }
}

module RealMedian refines Medians {
    type T = real

    function add(a: T, b: T):T {
        a+b
    }

    function halve(a: T):T {
        a/2.0
    }

    predicate Lte(a: T, b:T ) {
        a <= b
    }

    // Real averaging is exact, so the even-length median is a genuine median.
    lemma Averaging()
        ensures forall a: T, b: T :: Lte(a, b) ==> Lte(a, halve(add(a, b))) && Lte(halve(add(a, b)), b)
    {}
}

module TestMedians {
    import IM = IntMedian
    import BVM = BvMedian

    method Main() {
        var ints := [1,2,3,4,5];
        print "\nints := ", IM.Median(ints);
        var bvs: seq<bv8> := [1,2,3,4,5];
        print "\nbit vectors := ", BVM.Median(bvs);
    }
}
