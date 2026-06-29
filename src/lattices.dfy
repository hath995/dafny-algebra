// A lattice: two commutative, associative, idempotent operations -- join (\/) and
// meet (/\) -- linked by the two absorption laws. From these axioms ALONE the
// relation  a <= b  :<==>  a /\ b == a  is a partial order (reflexive, antisymmetric,
// transitive), proved below. That is the bridge between the algebraic and the
// order-theoretic views of a lattice.
abstract module Lattice {
    type T(==)
    function join(a: T, b: T): T    // least upper bound
    function meet(a: T, b: T): T    // greatest lower bound

    lemma JoinComm(a: T, b: T)        ensures join(a, b) == join(b, a)
    lemma JoinAssoc(a: T, b: T, c: T) ensures join(join(a, b), c) == join(a, join(b, c))
    lemma JoinIdem(a: T)              ensures join(a, a) == a
    lemma MeetComm(a: T, b: T)        ensures meet(a, b) == meet(b, a)
    lemma MeetAssoc(a: T, b: T, c: T) ensures meet(meet(a, b), c) == meet(a, meet(b, c))
    lemma MeetIdem(a: T)              ensures meet(a, a) == a
    lemma AbsorbJoin(a: T, b: T)      ensures join(a, meet(a, b)) == a
    lemma AbsorbMeet(a: T, b: T)      ensures meet(a, join(a, b)) == a

    // The induced order. The two characterizations agree (Consistency).
    ghost predicate Leq(a: T, b: T) { meet(a, b) == a }

    // a /\ b == a  <==>  a \/ b == b : the two ways to say "a <= b" coincide.
    lemma Consistency(a: T, b: T)
        ensures meet(a, b) == a <==> join(a, b) == b
    {
        if meet(a, b) == a {
            MeetComm(a, b);        // meet(b,a) == a
            AbsorbJoin(b, a);      // join(b, meet(b,a)) == b, i.e. join(b,a) == b
            JoinComm(a, b);        // join(a,b) == join(b,a) == b
        }
        if join(a, b) == b {
            AbsorbMeet(a, b);      // meet(a, join(a,b)) == a, i.e. meet(a,b) == a
        }
    }

    lemma LeqRefl(a: T)
        ensures Leq(a, a)
    {
        MeetIdem(a);
    }

    lemma LeqAntisym(a: T, b: T)
        requires Leq(a, b) && Leq(b, a)
        ensures a == b
    {
        MeetComm(a, b);            // a == meet(a,b) == meet(b,a) == b
    }

    lemma LeqTrans(a: T, b: T, c: T)
        requires Leq(a, b) && Leq(b, c)
        ensures Leq(a, c)
    {
        MeetAssoc(a, b, c);
        assert meet(a, c) == meet(meet(a, b), c);   // meet(a,b) == a
        assert meet(a, meet(b, c)) == meet(a, b);    // meet(b,c) == b
    }
}

// Adds the distributive laws. (In any lattice each implies the other; we take both
// as axioms so the instances just discharge them directly.)
abstract module DistributiveLattice refines Lattice {
    lemma DistribMeetJoin(a: T, b: T, c: T)
        ensures meet(a, join(b, c)) == join(meet(a, b), meet(a, c))
    lemma DistribJoinMeet(a: T, b: T, c: T)
        ensures join(a, meet(b, c)) == meet(join(a, b), join(a, c))

    // Cancellation: in a DISTRIBUTIVE lattice an element is pinned down by its meet
    // and join with any fixed element. (False in a general lattice.)
    lemma Cancellation(a: T, b: T, c: T)
        requires meet(a, b) == meet(a, c)
        requires join(a, b) == join(a, c)
        ensures b == c
    {
        calc {
            b;
            { AbsorbMeet(b, a); JoinComm(b, a); }   // b == meet(b, join(a,b))
            meet(b, join(a, b));
            // join(a,b) == join(a,c)
            meet(b, join(a, c));
            { DistribMeetJoin(b, a, c); }
            join(meet(b, a), meet(b, c));
            { MeetComm(b, a); }                      // meet(b,a) == meet(a,b) == meet(a,c)
            join(meet(a, c), meet(b, c));
            { MeetComm(a, c); MeetComm(b, c); }
            join(meet(c, a), meet(c, b));
            { DistribMeetJoin(c, a, b); }
            meet(c, join(a, b));
            // join(a,b) == join(a,c)
            meet(c, join(a, c));
            { JoinComm(a, c); AbsorbMeet(c, a); }    // meet(c, join(a,c)) == c
            c;
        }
    }
}

// Sets under union and intersection: the canonical distributive lattice.
module SetLattice refines DistributiveLattice {
    type T = set<int>
    function join(a: T, b: T): T { a + b }
    function meet(a: T, b: T): T { a * b }

    lemma JoinComm(a: T, b: T) {}
    lemma JoinAssoc(a: T, b: T, c: T) {}
    lemma JoinIdem(a: T) {}
    lemma MeetComm(a: T, b: T) {}
    lemma MeetAssoc(a: T, b: T, c: T) {}
    lemma MeetIdem(a: T) {}
    lemma AbsorbJoin(a: T, b: T) {}
    lemma AbsorbMeet(a: T, b: T) {}
    lemma DistribMeetJoin(a: T, b: T, c: T) {}
    lemma DistribJoinMeet(a: T, b: T, c: T) {}
}

// A totally ordered set (here the integers) under max and min: a chain, hence a
// distributive lattice. Here Leq is exactly the usual <=.
module MinMaxLattice refines DistributiveLattice {
    type T = int
    function join(a: T, b: T): T { if a >= b then a else b }   // max
    function meet(a: T, b: T): T { if a <= b then a else b }    // min

    lemma JoinComm(a: T, b: T) {}
    lemma JoinAssoc(a: T, b: T, c: T) {}
    lemma JoinIdem(a: T) {}
    lemma MeetComm(a: T, b: T) {}
    lemma MeetAssoc(a: T, b: T, c: T) {}
    lemma MeetIdem(a: T) {}
    lemma AbsorbJoin(a: T, b: T) {}
    lemma AbsorbMeet(a: T, b: T) {}
    lemma DistribMeetJoin(a: T, b: T, c: T) {}
    lemma DistribJoinMeet(a: T, b: T, c: T) {}
}

// A Boolean algebra: a distributive lattice with a least element Bot (0), a
// greatest element Top (1), and a complement. From the axioms below, complements
// are UNIQUE (using the distributive-lattice Cancellation lemma), and the rest of
// Boolean algebra -- double complement and De Morgan -- follows.
abstract module BooleanAlgebra refines DistributiveLattice {
    function Top(): T   // greatest element (1)
    function Bot(): T   // least element (0)
    function Compl(a: T): T

    lemma JoinBot(a: T)   ensures join(a, Bot()) == a       // Bot is the identity of join
    lemma MeetTop(a: T)   ensures meet(a, Top()) == a       // Top is the identity of meet
    lemma JoinCompl(a: T) ensures join(a, Compl(a)) == Top()
    lemma MeetCompl(a: T) ensures meet(a, Compl(a)) == Bot()

    // Bot annihilates meet and Top annihilates join (Bot <= everything <= Top).
    lemma MeetBot(a: T)
        ensures meet(Bot(), a) == Bot() && meet(a, Bot()) == Bot()
    {
        JoinBot(a); JoinComm(Bot(), a);   // join(Bot,a) == join(a,Bot) == a
        Consistency(Bot(), a);            // meet(Bot,a)==Bot <==> join(Bot,a)==a
        MeetComm(a, Bot());
    }

    lemma JoinTop(a: T)
        ensures join(a, Top()) == Top() && join(Top(), a) == Top()
    {
        MeetTop(a);                       // meet(a,Top())==a
        Consistency(a, Top());            // meet(a,Top)==a <==> join(a,Top)==Top
        JoinComm(Top(), a);
    }

    // Complements are unique: anything that joins to Top and meets to Bot with a
    // IS a's complement. This is exactly the distributive Cancellation law.
    lemma ComplUnique(a: T, x: T)
        requires join(a, x) == Top() && meet(a, x) == Bot()
        ensures x == Compl(a)
    {
        JoinCompl(a); MeetCompl(a);   // join(a,Compl(a))==Top()==join(a,x); meet likewise==Bot()
        Cancellation(a, x, Compl(a));
    }

    // Involution: the complement of the complement is the original.
    lemma ComplCompl(a: T)
        ensures Compl(Compl(a)) == a
    {
        JoinCompl(a); JoinComm(a, Compl(a));   // join(Compl(a), a) == Top()
        MeetCompl(a); MeetComm(a, Compl(a));   // meet(Compl(a), a) == Bot()
        ComplUnique(Compl(a), a);
    }

    // De Morgan: the complement of a join is the meet of the complements.
    lemma DeMorganJoin(a: T, b: T)
        ensures Compl(join(a, b)) == meet(Compl(a), Compl(b))
    {
        var m := meet(Compl(a), Compl(b));
        // join(join(a,b), m) == Top()
        calc {
            join(join(a, b), m);
            { DistribJoinMeet(join(a, b), Compl(a), Compl(b)); }
            meet(join(join(a, b), Compl(a)), join(join(a, b), Compl(b)));
            { JoinComm(a, b); JoinAssoc(b, a, Compl(a)); JoinCompl(a); JoinTop(b); }
            meet(Top(), join(join(a, b), Compl(b)));
            { JoinAssoc(a, b, Compl(b)); JoinCompl(b); JoinTop(a); }
            meet(Top(), Top());
            { MeetIdem(Top()); }
            Top();
        }
        // meet(join(a,b), m) == Bot()
        calc {
            meet(join(a, b), m);
            { MeetComm(join(a, b), m); DistribMeetJoin(m, a, b); }
            join(meet(m, a), meet(m, b));
            { MeetComm(Compl(a), Compl(b)); MeetAssoc(Compl(b), Compl(a), a);
              MeetCompl(a); MeetComm(a, Compl(a)); MeetBot(Compl(b)); }
            join(Bot(), meet(m, b));
            { MeetAssoc(Compl(a), Compl(b), b); MeetCompl(b); MeetComm(b, Compl(b)); MeetBot(Compl(a)); }
            join(Bot(), Bot());
            { JoinIdem(Bot()); }
            Bot();
        }
        ComplUnique(join(a, b), m);
    }

    // ...and dually, the complement of a meet is the join of the complements.
    lemma DeMorganMeet(a: T, b: T)
        ensures Compl(meet(a, b)) == join(Compl(a), Compl(b))
    {
        DeMorganJoin(Compl(a), Compl(b));   // Compl(join(Compl a, Compl b)) == meet(a,b)
        ComplCompl(a); ComplCompl(b);
        var x := join(Compl(a), Compl(b));
        ComplCompl(x);                      // Compl(Compl(x)) == x; Compl(x) == meet(a,b)
    }
}

// The two-element Boolean algebra: the Booleans under OR/AND, with negation.
module BoolAlgebra refines BooleanAlgebra {
    type T = bool
    function join(a: T, b: T): T { a || b }
    function meet(a: T, b: T): T { a && b }
    function Top(): T { true }
    function Bot(): T { false }
    function Compl(a: T): T { !a }

    lemma JoinComm(a: T, b: T) {}
    lemma JoinAssoc(a: T, b: T, c: T) {}
    lemma JoinIdem(a: T) {}
    lemma MeetComm(a: T, b: T) {}
    lemma MeetAssoc(a: T, b: T, c: T) {}
    lemma MeetIdem(a: T) {}
    lemma AbsorbJoin(a: T, b: T) {}
    lemma AbsorbMeet(a: T, b: T) {}
    lemma DistribMeetJoin(a: T, b: T, c: T) {}
    lemma DistribJoinMeet(a: T, b: T, c: T) {}
    lemma JoinBot(a: T) {}
    lemma MeetTop(a: T) {}
    lemma JoinCompl(a: T) {}
    lemma MeetCompl(a: T) {}
}

// The powerset of a finite universe is a Boolean algebra. Booleans have exactly
// two values, so set<bool> is the 4-element powerset of {false,true}, with the
// complement taken relative to that full universe.
module PowersetAlgebra refines BooleanAlgebra {
    type T = set<bool>
    function join(a: T, b: T): T { a + b }
    function meet(a: T, b: T): T { a * b }
    function Top(): T { {false, true} }
    function Bot(): T { {} }
    function Compl(a: T): T { {false, true} - a }

    lemma JoinComm(a: T, b: T) {}
    lemma JoinAssoc(a: T, b: T, c: T) {}
    lemma JoinIdem(a: T) {}
    lemma MeetComm(a: T, b: T) {}
    lemma MeetAssoc(a: T, b: T, c: T) {}
    lemma MeetIdem(a: T) {}
    lemma AbsorbJoin(a: T, b: T) {}
    lemma AbsorbMeet(a: T, b: T) {}
    lemma DistribMeetJoin(a: T, b: T, c: T) {}
    lemma DistribJoinMeet(a: T, b: T, c: T) {}
    // Every bool lies in the universe {false,true}, so a is always a subset of Top.
    lemma InUniverse(a: T)
        ensures a <= {false, true}
    {
        forall x | x in a ensures x == false || x == true {}
    }

    lemma JoinBot(a: T) {}
    lemma MeetTop(a: T) { InUniverse(a); }       // a * {f,t} == a since a <= {f,t}
    lemma JoinCompl(a: T) { InUniverse(a); }     // a + ({f,t} - a) == {f,t}
    lemma MeetCompl(a: T) {}
}

// A meet-semilattice: ONE commutative, associative, idempotent operation. It
// induces the same partial order a <= b :<==> op(a,b) == a as a lattice, and op
// is the greatest lower bound. A Lattice is two semilattices (join and meet)
// glued by absorption; this is the single-operation fragment.
abstract module Semilattice {
    type T(==)
    function op(a: T, b: T): T
    lemma Comm(a: T, b: T)        ensures op(a, b) == op(b, a)
    lemma Assoc(a: T, b: T, c: T) ensures op(op(a, b), c) == op(a, op(b, c))
    lemma Idem(a: T)              ensures op(a, a) == a

    ghost predicate Leq(a: T, b: T) { op(a, b) == a }

    lemma LeqRefl(a: T)
        ensures Leq(a, a)
    {
        Idem(a);
    }

    lemma LeqAntisym(a: T, b: T)
        requires Leq(a, b) && Leq(b, a)
        ensures a == b
    {
        Comm(a, b);   // a == op(a,b) == op(b,a) == b
    }

    lemma LeqTrans(a: T, b: T, c: T)
        requires Leq(a, b) && Leq(b, c)
        ensures Leq(a, c)
    {
        calc {
            op(a, c);
            op(op(a, b), c);        // a == op(a,b)
            { Assoc(a, b, c); }
            op(a, op(b, c));
            op(a, b);               // op(b,c) == b
            a;
        }
    }

    // op is a lower bound of both arguments...
    lemma OpLowerLeft(a: T, b: T)
        ensures Leq(op(a, b), a)
    {
        calc {
            op(op(a, b), a);
            { Comm(a, b); }
            op(op(b, a), a);
            { Assoc(b, a, a); }
            op(b, op(a, a));
            { Idem(a); }
            op(b, a);
            { Comm(b, a); }
            op(a, b);
        }
    }

    lemma OpLowerRight(a: T, b: T)
        ensures Leq(op(a, b), b)
    {
        calc {
            op(op(a, b), b);
            { Assoc(a, b, b); }
            op(a, op(b, b));
            { Idem(b); }
            op(a, b);
        }
    }

    // ...and the GREATEST such: any common lower bound c is below op(a,b).
    lemma OpGreatest(a: T, b: T, c: T)
        requires Leq(c, a) && Leq(c, b)
        ensures Leq(c, op(a, b))
    {
        calc {
            op(c, op(a, b));
            { Assoc(c, a, b); }
            op(op(c, a), b);
            op(c, b);    // op(c,a) == c
            c;           // op(c,b) == c
        }
    }
}

// The integers under min: the prototypical (meet-)semilattice. Leq is the usual <=.
module MinSemilattice refines Semilattice {
    type T = int
    function op(a: T, b: T): T { if a <= b then a else b }   // min

    lemma Comm(a: T, b: T) {}
    lemma Assoc(a: T, b: T, c: T) {}
    lemma Idem(a: T) {}
}
