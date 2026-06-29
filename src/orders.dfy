include "lattices.dfy"

// The order-theoretic hierarchy as a refinement chain on a single relation Leq:
//
//     Preorder -> PartialOrder -> TotalOrder
//
// Each step adds one law, mirroring the algebraic chain in algebra.dfy. The
// induced order of a Lattice (lattices.dfy) is, by its proved laws, a partial
// order; a TotalOrder is the extra "any two are comparable" on top of that.
abstract module Preorder {
    type T(==, !new)
    // Compiled (not ghost) so it can be turned into a relation value and used by
    // executable code such as the sorts behind median.dfy and fold.dfy.
    predicate Leq(a: T, b: T)

    lemma Refl(a: T)
        ensures Leq(a, a)
    lemma Trans(a: T, b: T, c: T)
        requires Leq(a, b) && Leq(b, c)
        ensures Leq(a, c)

    // The strict part of the order. Irreflexive by construction.
    ghost predicate Lt(a: T, b: T) { Leq(a, b) && a != b }

    lemma LtIrrefl(a: T)
        ensures !Lt(a, a)
    {}
}

abstract module PartialOrder refines Preorder {
    lemma Antisym(a: T, b: T)
        requires Leq(a, b) && Leq(b, a)
        ensures a == b

    // The strict order is transitive and asymmetric (both need antisymmetry).
    lemma LtTrans(a: T, b: T, c: T)
        requires Lt(a, b) && Lt(b, c)
        ensures Lt(a, c)
    {
        Trans(a, b, c);
        if a == c {
            Antisym(b, c);   // Leq(c,b)==Leq(a,b) and Leq(b,c) ==> b==c, contradicting Lt(b,c)
        }
    }

    lemma LtAsym(a: T, b: T)
        requires Lt(a, b)
        ensures !Lt(b, a)
    {
        if Leq(b, a) {
            Antisym(a, b);   // Leq(a,b) && Leq(b,a) ==> a==b, contradicting Lt(a,b)
        }
    }
}

abstract module TotalOrder refines PartialOrder {
    lemma Total(a: T, b: T)
        ensures Leq(a, b) || Leq(b, a)

    // Trichotomy: at least one of a < b, a == b, b < a holds.
    lemma Trichotomy(a: T, b: T)
        ensures Lt(a, b) || a == b || Lt(b, a)
    {
        Total(a, b);
    }

    // ---- a verified merge sort over the order, available to every TotalOrder ----
    // Sorting needs exactly a total order, so it lives here rather than in any one
    // client (e.g. medians). It is written directly against Leq and its laws -- no
    // relation parameter, no standard-library dependency.

    ghost predicate SortedBy(s: seq<T>) {
        forall i, j :: 0 <= i < j < |s| ==> Leq(s[i], s[j])
    }

    // In a sorted sequence the head is Leq every element (reflexive at the head).
    lemma HeadIsLeast(s: seq<T>)
        requires SortedBy(s) && |s| > 0
        ensures forall e :: e in s ==> Leq(s[0], e)
    {
        forall e | e in s ensures Leq(s[0], e) {
            var k :| 0 <= k < |s| && s[k] == e;
            if k == 0 { Refl(s[0]); }   // k > 0 is SortedBy
        }
    }

    // ...hence the head is Leq every element of the tail.
    lemma TailBounded(s: seq<T>)
        requires SortedBy(s) && |s| > 0
        ensures forall e :: e in s[1..] ==> Leq(s[0], e)
    {
        HeadIsLeast(s);
        assert s == [s[0]] + s[1..];   // e in s[1..] ==> e in s
    }

    // Prepending an element below all of a sorted sequence keeps it sorted.
    lemma PrependBelow(x: T, s: seq<T>)
        requires SortedBy(s)
        requires forall e :: e in s ==> Leq(x, e)
        ensures SortedBy([x] + s)
    {
        var r := [x] + s;
        forall i, j | 0 <= i < j < |r| ensures Leq(r[i], r[j]) {
            if i == 0 {
                assert r[j] == s[j-1] && s[j-1] in s;   // Leq(x, s[j-1])
            } else {
                assert r[i] == s[i-1] && r[j] == s[j-1];   // SortedBy(s)
            }
        }
    }

    // If a pivot is Leq its own (sorted) tail and Leq the other (sorted) sequence's
    // head, then it is Leq every element of their merge.
    lemma MergeBelow(pivot: T, pivotTail: seq<T>, other: seq<T>, merged: seq<T>)
        requires SortedBy(pivotTail) && SortedBy(other)
        requires forall e :: e in pivotTail ==> Leq(pivot, e)
        requires |other| == 0 || Leq(pivot, other[0])
        requires multiset(merged) == multiset(pivotTail) + multiset(other)
        ensures forall e :: e in merged ==> Leq(pivot, e)
    {
        if |other| > 0 {
            HeadIsLeast(other);
            forall e | e in other ensures Leq(pivot, e) { Trans(pivot, other[0], e); }
        }
        forall e | e in merged ensures Leq(pivot, e) {
            assert e in multiset(merged);                          // seq membership ==> multiset
            assert e in multiset(pivotTail) || e in multiset(other);
        }
    }

    // Merge two sorted sequences into one, preserving elements.
    function MergeWith(left: seq<T>, right: seq<T>): (result: seq<T>)
        requires SortedBy(left) && SortedBy(right)
        ensures multiset(result) == multiset(left) + multiset(right)
        ensures |result| == |left| + |right|
        ensures SortedBy(result)
        decreases |left| + |right|
    {
        if |left| == 0 then right
        else if |right| == 0 then left
        else if Leq(left[0], right[0]) then
            var merged := MergeWith(left[1..], right);
            assert left == [left[0]] + left[1..];
            TailBounded(left);
            MergeBelow(left[0], left[1..], right, merged);
            PrependBelow(left[0], merged);
            [left[0]] + merged
        else
            Total(left[0], right[0]);   // !Leq(left[0],right[0]) ==> Leq(right[0],left[0])
            var merged := MergeWith(left, right[1..]);
            assert right == [right[0]] + right[1..];
            TailBounded(right);
            MergeBelow(right[0], right[1..], left, merged);
            PrependBelow(right[0], merged);
            [right[0]] + merged
    }

    // Recursive merge sort: the data sorted by the order. No order hypothesis
    // needed -- Leq and its laws are part of the module.
    function Sorted(xs: seq<T>): (ss: seq<T>)
        ensures multiset(ss) == multiset(xs)
        ensures |ss| == |xs|
        ensures SortedBy(ss)
        decreases |xs|
    {
        if |xs| <= 1 then xs
        else
            var mid := |xs| / 2;
            assert xs == xs[..mid] + xs[mid..];
            MergeWith(Sorted(xs[..mid]), Sorted(xs[mid..]))
    }

    // Two sequences that are sorted and have the same elements are identical: a
    // total order admits a UNIQUE sorted arrangement of any multiset. (The heads
    // are forced equal -- each is the minimum of the common multiset, pinned by
    // antisymmetry -- then recurse.)
    lemma SortedUnique(xs: seq<T>, ys: seq<T>)
        requires SortedBy(xs) && SortedBy(ys)
        requires multiset(xs) == multiset(ys)
        ensures xs == ys
        decreases |xs|
    {
        if xs != [] {
            assert xs == [xs[0]] + xs[1..];
            assert ys == [ys[0]] + ys[1..];
            assert multiset(xs) == multiset{xs[0]} + multiset(xs[1..]);
            assert multiset(ys) == multiset{ys[0]} + multiset(ys[1..]);
            // both heads live in the shared multiset, hence in the other sequence
            assert xs[0] in multiset(ys) && ys[0] in multiset(xs);
            assert xs[0] in ys && ys[0] in xs;
            HeadIsLeast(xs);                       // xs[0] <= ys[0] (ys[0] in xs)
            HeadIsLeast(ys);                       // ys[0] <= xs[0] (xs[0] in ys)
            Antisym(xs[0], ys[0]);                 // ==> xs[0] == ys[0]
            assert multiset(xs[1..]) == multiset(xs) - multiset{xs[0]};
            assert multiset(ys[1..]) == multiset(ys) - multiset{ys[0]};
            assert multiset(xs[1..]) == multiset(ys[1..]);   // equal heads cancel
            SortedUnique(xs[1..], ys[1..]);
        }
    }
}

// The integers under <= : the prototypical total order.
module IntOrder refines TotalOrder {
    type T = int
    predicate Leq(a: T, b: T) { a <= b }

    lemma Refl(a: T) {}
    lemma Trans(a: T, b: T, c: T) {}
    lemma Antisym(a: T, b: T) {}
    lemma Total(a: T, b: T) {}
}

// A bounded lattice: a lattice with a top (greatest) and bottom (least) element.
// From the two identity laws below, Bot is <= everything and Top is >= everything
// in the lattice's induced order -- proved once here.
abstract module BoundedLattice refines Lattice {
    function Top(): T
    function Bot(): T

    lemma JoinBot(a: T) ensures join(a, Bot()) == a   // Bot is the identity of join
    lemma MeetTop(a: T) ensures meet(a, Top()) == a   // Top is the identity of meet

    lemma BotLeast(a: T)
        ensures Leq(Bot(), a)
    {
        JoinBot(a); JoinComm(Bot(), a);   // join(Bot,a) == a
        Consistency(Bot(), a);            // meet(Bot,a)==Bot <==> join(Bot,a)==a
    }

    lemma TopGreatest(a: T)
        ensures Leq(a, Top())
    {
        MeetTop(a);   // Leq(a,Top()) is meet(a,Top())==a
    }
}

// The powerset of {false,true} (= set<bool>) under union/intersection: a bounded
// lattice with Top the full universe and Bot the empty set.
module BoolSetLattice refines BoundedLattice {
    type T = set<bool>
    function join(a: T, b: T): T { a + b }
    function meet(a: T, b: T): T { a * b }
    function Top(): T { {false, true} }
    function Bot(): T { {} }

    lemma JoinComm(a: T, b: T) {}
    lemma JoinAssoc(a: T, b: T, c: T) {}
    lemma JoinIdem(a: T) {}
    lemma MeetComm(a: T, b: T) {}
    lemma MeetAssoc(a: T, b: T, c: T) {}
    lemma MeetIdem(a: T) {}
    lemma AbsorbJoin(a: T, b: T) {}
    lemma AbsorbMeet(a: T, b: T) {}
    lemma JoinBot(a: T) {}
    lemma MeetTop(a: T) {
        forall x | x in a ensures x == false || x == true {}   // a <= {false,true}
    }
}
