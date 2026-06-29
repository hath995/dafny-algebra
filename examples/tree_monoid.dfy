include "../src/algebra.dfy"
include "../src/orders.dfy"

// EXAMPLE: a binary tree as the meeting point of TWO of our structures.
//
//   * Tree<A> is a MONOID under composition `comp` with `Nil` as identity
//     (src/algebra.dfy's Monoid), and
//   * its element type is a TOTAL ORDER (src/orders.dfy's TotalOrder), which gives
//     a verified merge sort on the leaves.
//
// Unlike the integers -- where every structure law is already known to the
// verifier as arithmetic -- NONE of these laws is free: composition's
// associativity, the flatten homomorphism, and sortedness are all genuine
// inductive proofs. So the capstone really does NEED both structures' lemmas:
//
//     sort(leaves(s `comp` t))  ==  merge(sort(leaves s), sort(leaves t))
//
// "sorting a composition = merging the sorted parts" -- the Monoid side supplies
// the homomorphism leaves(s comp t) = leaves(s) ++ leaves(t); the TotalOrder side
// supplies MergeWith, Sorted, and the uniqueness of sorted arrangements.

module Trees {
    datatype Tree<A> = Nil | Leaf(x: A) | Node(left: Tree<A>, right: Tree<A>)

    // Composition grafts t2 onto the right spine of t1; Nil is a two-sided identity.
    function comp<A>(t1: Tree<A>, t2: Tree<A>): Tree<A> {
        match t1
        case Nil => t2
        case Leaf(_) => if t2 == Nil then t1 else Node(t1, t2)
        case Node(l, r) => if t2 == Nil then t1 else Node(l, comp(r, t2))
    }

    // The in-order sequence of leaves.
    function flatten<A>(t: Tree<A>): seq<A> {
        match t
        case Nil => []
        case Leaf(x) => [x]
        case Node(l, r) => flatten(l) + flatten(r)
    }

    lemma CompLeftId<A>(t: Tree<A>)  ensures comp(Nil, t) == t {}
    lemma CompRightId<A>(t: Tree<A>) ensures comp(t, Nil) == t {}

    // Composition is associative (a real structural induction -- not free).
    lemma CompAssoc<A>(a: Tree<A>, b: Tree<A>, c: Tree<A>)
        ensures comp(comp(a, b), c) == comp(a, comp(b, c))
    {
        match a
        case Nil =>
        case Leaf(_) =>
        case Node(l, r) => CompAssoc(r, b, c);
    }

    // `flatten` is a monoid homomorphism (Tree, comp, Nil) -> (seq, +, []).
    lemma FlattenHomOp<A>(s: Tree<A>, t: Tree<A>)
        ensures flatten(comp(s, t)) == flatten(s) + flatten(t)
    {
        match s
        case Nil =>
        case Leaf(_) =>
        case Node(l, r) => FlattenHomOp(r, t);
    }
}

// STRUCTURE 1: trees over int form a Monoid. The instance discharges the Monoid
// laws using the tree lemmas above (and inherits Monoid's derived `pow`, `PowAdd`,
// ... for free).
module TreeMonoid refines Monoid {
    import opened Trees
    type T = Tree<int>

    function op(a: T, b: T): T { comp(a, b) }
    function Id(): T { Nil }

    lemma Assoc(a: T, b: T, c: T) { CompAssoc(a, b, c); }
    lemma LeftId(a: T) {}    // comp(Nil, a) == a
    lemma RightId(a: T) {}   // comp(a, Nil) == a
}

// Bring the two structures together. STRUCTURE 2 is the element order, IntOrder
// (a TotalOrder), whose inherited merge sort (Sorted / MergeWith / SortedUnique)
// we use on the leaves.
module SortedTrees {
    import opened Trees
    import M = TreeMonoid   // trees as a Monoid
    import O = IntOrder     // elements as a TotalOrder

    // The leaves of a tree, sorted by the element order.
    function SortLeaves(t: Tree<int>): seq<int> {
        O.Sorted(flatten(t))
    }

    // CAPSTONE: sorting the leaves of a composition equals merging the sorted
    // leaves of the parts. Needs the Monoid homomorphism (FlattenHomOp, with
    // M.op == comp) AND the TotalOrder's sort machinery (Sorted, MergeWith, and
    // SortedUnique to identify two equal-multiset sorted sequences).
    lemma SortLeavesOfComposition(s: Tree<int>, t: Tree<int>)
        ensures SortLeaves(M.op(s, t)) == O.MergeWith(SortLeaves(s), SortLeaves(t))
    {
        FlattenHomOp(s, t);   // flatten(M.op(s,t)) == flatten(s) + flatten(t)

        var lhs := SortLeaves(M.op(s, t));
        var merged := O.MergeWith(SortLeaves(s), SortLeaves(t));

        // both sides are sorted...
        assert O.SortedBy(lhs);      // Sorted's postcondition
        assert O.SortedBy(merged);   // MergeWith's postcondition

        // ...and carry the same multiset of elements...
        assert multiset(flatten(M.op(s, t))) == multiset(flatten(s)) + multiset(flatten(t));
        assert multiset(lhs) == multiset(flatten(s)) + multiset(flatten(t));
        assert multiset(merged) == multiset(SortLeaves(s)) + multiset(SortLeaves(t));
        assert multiset(SortLeaves(s)) == multiset(flatten(s));
        assert multiset(SortLeaves(t)) == multiset(flatten(t));
        assert multiset(lhs) == multiset(merged);

        // ...so a total order's unique sorted arrangement makes them identical.
        O.SortedUnique(lhs, merged);
    }

    // The MONOID law itself shows through the sort: associating composition either
    // way yields the same sorted leaves. Proof rests on M.Assoc (comp's
    // associativity, an inductive tree lemma) plus determinism of Sorted.
    lemma SortRespectsAssociativity(a: Tree<int>, b: Tree<int>, c: Tree<int>)
        ensures SortLeaves(M.op(M.op(a, b), c)) == SortLeaves(M.op(a, M.op(b, c)))
    {
        M.Assoc(a, b, c);   // M.op(M.op(a,b),c) == M.op(a,M.op(b,c))
    }

    // ...and the identity element contributes no leaves (homomorphism preserves 1).
    lemma SortIgnoresIdentity(t: Tree<int>)
        ensures SortLeaves(M.op(t, M.Id())) == SortLeaves(t)
    {
        M.RightId(t);   // M.op(t, Nil) == t
    }

    @Test
    method test() {
        var s := Node(Leaf(3), Leaf(1));   // leaves 3, 1
        var t := Leaf(2);                  // leaf 2
        SortLeavesOfComposition(s, t);
        print "sort(leaves(s comp t)) = ", SortLeaves(M.op(s, t)), "\n";
        print "merge(sort s, sort t)  = ", O.MergeWith(SortLeaves(s), SortLeaves(t)), "\n";
    }
}
