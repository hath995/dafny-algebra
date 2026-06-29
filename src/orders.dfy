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
    ghost predicate Leq(a: T, b: T)

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
}

// The integers under <= : the prototypical total order.
module IntOrder refines TotalOrder {
    type T = int
    ghost predicate Leq(a: T, b: T) { a <= b }

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
