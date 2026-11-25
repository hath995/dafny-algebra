include "orders.dfy"

// Medians, built on the order hierarchy: a Medians module IS a TotalOrder (it
// refines orders.dfy's TotalOrder), so it inherits the comparison Leq, the four
// order laws (Refl/Trans/Antisym/Total), AND the verified merge sort (Sorted /
// SortedBy) defined there -- no `TotalOrdering(Lte)` hypothesis, no standard
// library. All that is added here is averaging (add/halve) and the median itself.
abstract module Medians refines TotalOrder {

    function add(a: T, b: T): T
    function halve(a: T): T

    function Median(xs: seq<T>): T
        requires |xs| > 0
    {
        var ss := Sorted(xs);
        if |ss| % 2 == 0 then halve(add(ss[|ss|/2 - 1], ss[|ss|/2])) else ss[|ss|/2]
    }

    // A median splits the (sorted) data: everything up to the middle is Leq it,
    // and everything from the middle on is Geq it. For odd length the Median is
    // exactly the middle order statistic, so this holds with no assumptions
    // beyond the inherited order being total.
    lemma MedianSplitsOdd(xs: seq<T>)
        requires |xs| > 0 && |xs| % 2 == 1
        ensures var ss := Sorted(xs);
            && Median(xs) == ss[|xs|/2]
            && (forall i :: 0 <= i <= |xs|/2 ==> Leq(ss[i], Median(xs)))     // lower half (and middle) <= median
            && (forall i :: |xs|/2 <= i < |xs| ==> Leq(Median(xs), ss[i]))   // middle (and upper half) >= median
    {
        var ss := Sorted(xs);                    // SortedBy(ss); Leq is reflexive at the middle
        Refl(ss[|xs|/2]);
    }

    // The claim about the *original* (unsorted) data: at least half of xs is Leq
    // the median, and at least half is Geq it -- the rank/balance definition. The
    // witnesses are the lower/upper halves of the sorted data, sub-multisets of
    // xs because multiset(ss) == multiset(xs).
    lemma MedianBalanceOdd(xs: seq<T>)
        requires |xs| > 0 && |xs| % 2 == 1
        ensures exists lo :: lo <= multiset(xs) && |lo| == (|xs|+1)/2 && (forall e :: e in lo ==> Leq(e, Median(xs)))
        ensures exists hi :: hi <= multiset(xs) && |hi| == (|xs|+1)/2 && (forall e :: e in hi ==> Leq(Median(xs), e))
    {
        var ss := Sorted(xs);
        var mid := |xs| / 2;
        assert Median(xs) == ss[mid];
        assert SortedBy(ss);
        assert |ss| == |xs|;

        var lo := multiset(ss[..mid+1]);
        assert ss[..mid+1] + ss[mid+1..] == ss;
        assert multiset(xs) == lo + multiset(ss[mid+1..]);      // lo <= multiset(xs)
        forall e | e in lo ensures Leq(e, Median(xs)) {
            var k :| 0 <= k < mid+1 && ss[..mid+1][k] == e;     // e is some ss[k], k <= mid
            assert ss[k] == e;
            Refl(ss[mid]);                                      // covers k == mid; k < mid is SortedBy
        }

        var hi := multiset(ss[mid..]);
        assert ss[..mid] + ss[mid..] == ss;
        assert multiset(xs) == multiset(ss[..mid]) + hi;        // hi <= multiset(xs)
        forall e | e in hi ensures Leq(Median(xs), e) {
            var k :| 0 <= k < |ss[mid..]| && ss[mid..][k] == e; // e is some ss[mid+k], mid+k >= mid
            assert ss[mid + k] == e;
        }
    }

    // For even length the Median is the average of the two central order
    // statistics, which is a median provided averaging stays between its inputs
    // (true for int/real; fails for bv8 on overflow). That property is taken as
    // a hypothesis here and discharged by the concrete refinements below.
    lemma MedianSplitsEven(xs: seq<T>)
        requires |xs| > 0 && |xs| % 2 == 0
        requires forall a, b :: Leq(a, b) ==> Leq(a, halve(add(a, b))) && Leq(halve(add(a, b)), b)
        ensures var ss := Sorted(xs);
            && Median(xs) == halve(add(ss[|xs|/2 - 1], ss[|xs|/2]))
            && Leq(ss[|xs|/2 - 1], Median(xs))    // lower central <= median
            && Leq(Median(xs), ss[|xs|/2])        // median <= upper central
    {
        var ss := Sorted(xs);
        assert SortedBy(ss);                      // so Leq(ss[mid-1], ss[mid]) for the two centrals
    }
}

module IntMedian refines Medians {
    type T = int

    function add(a: T, b: T): T { a + b }
    function halve(a: T): T { a / 2 }
    predicate Leq(a: T, b: T) { a <= b }

    lemma Refl(a: T) {}
    lemma Trans(a: T, b: T, c: T) {}
    lemma Antisym(a: T, b: T) {}
    lemma Total(a: T, b: T) {}

    // Integer (floor) averaging stays between its inputs, so the even-length
    // median is a genuine median.
    lemma Averaging()
        ensures forall a: T, b: T :: Leq(a, b) ==> Leq(a, halve(add(a, b))) && Leq(halve(add(a, b)), b)
    {}
}

module BvMedian refines Medians {
    type T = bv8

    function add(a: T, b: T): T { a + b }
    function halve(a: T): T { a >> 1 }
    predicate Leq(a: T, b: T) { a <= b }

    lemma Refl(a: T) {}
    lemma Trans(a: T, b: T, c: T) {}
    lemma Antisym(a: T, b: T) {}
    lemma Total(a: T, b: T) {}
}

module RealMedian refines Medians {
    type T = real

    function add(a: T, b: T): T { a + b }
    function halve(a: T): T { a / 2.0 }
    predicate Leq(a: T, b: T) { a <= b }

    lemma Refl(a: T) {}
    lemma Trans(a: T, b: T, c: T) {}
    lemma Antisym(a: T, b: T) {}
    lemma Total(a: T, b: T) {}

    // Real averaging is exact, so the even-length median is a genuine median.
    lemma Averaging()
        ensures forall a: T, b: T :: Leq(a, b) ==> Leq(a, halve(add(a, b))) && Leq(halve(add(a, b)), b)
    {}
}