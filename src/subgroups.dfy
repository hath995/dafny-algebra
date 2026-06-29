include "algebra.dfy"
include "collections.dfy"

// Subgroup theory parameterized by BOTH the group (import G) and the collection
// type (import L) — the latter abstracts set vs iset, so the whole theory is
// written once and reused by the finite and infinite instantiations.
abstract module Subgroups {
    import G : Group
    import L : Collection

    ghost predicate IsSubgroup(s: L.C<G.T>) {
        && L.In(G.Id(), s)
        && (forall a, b :: L.In(a, s) && L.In(b, s) ==> L.In(G.op(a, b), s))
        && (forall a :: L.In(a, s) ==> L.In(G.Inv(a), s))
    }

    // {e} is a subgroup — written once; works for finite (set) and infinite (iset).
    lemma TrivialSubgroup()
        ensures IsSubgroup(L.Single(G.Id()))
    {
        L.SingleChar(G.Id(), G.Id());
        G.LeftId(G.Id());
        G.InvId();
        forall a, b | L.In(a, L.Single(G.Id())) && L.In(b, L.Single(G.Id()))
            ensures L.In(G.op(a, b), L.Single(G.Id()))
        {
            L.SingleChar(G.Id(), a);
            L.SingleChar(G.Id(), b);
            L.SingleChar(G.Id(), G.op(a, b));
        }
        forall a | L.In(a, L.Single(G.Id()))
            ensures L.In(G.Inv(a), L.Single(G.Id()))
        {
            L.SingleChar(G.Id(), a);
            L.SingleChar(G.Id(), G.Inv(a));
        }
    }

    // The intersection of two subgroups is a subgroup.
    lemma SubgroupIntersect(s: L.C<G.T>, t: L.C<G.T>)
        requires IsSubgroup(s) && IsSubgroup(t)
        ensures IsSubgroup(L.Inter(s, t))
    {
        L.InterChar(s, t, G.Id());
        forall a, b | L.In(a, L.Inter(s, t)) && L.In(b, L.Inter(s, t))
            ensures L.In(G.op(a, b), L.Inter(s, t))
        {
            L.InterChar(s, t, a);
            L.InterChar(s, t, b);
            L.InterChar(s, t, G.op(a, b));
        }
        forall a | L.In(a, L.Inter(s, t))
            ensures L.In(G.Inv(a), L.Inter(s, t))
        {
            L.InterChar(s, t, a);
            L.InterChar(s, t, G.Inv(a));
        }
    }

    // A subgroup is closed under (natural) powers of its elements.
    lemma SubgroupClosedUnderPow(s: L.C<G.T>, a: G.T, n: nat)
        requires IsSubgroup(s) && L.In(a, s)
        ensures L.In(G.pow(a, n), s)
        decreases n
    {
        if n != 0 {
            SubgroupClosedUnderPow(s, a, n-1);   // a^(n-1) in s, a in s, so op(a^(n-1), a) in s
        }
    }
}

// Fully concrete: subgroups of the integers' additive group, finite and infinite.
module IntSetSubgroups refines Subgroups {
    import G = IntRing
    import L = SetColl
}
module IntISetSubgroups refines Subgroups {
    import G = IntRing
    import L = ISetColl

    // nZ = { n*k : k in Z } is a subgroup of (Z, +).
    lemma MultiplesSubgroup(n: int)
        ensures IsSubgroup(iset x: int | exists k :: x == n * k)
    {
        var s := iset x: int | exists k :: x == n * k;
        assert 0 == n * 0;                                   // identity: 0 in nZ
        forall a, b | L.In(a, s) && L.In(b, s)
            ensures L.In(G.op(a, b), s)
        {
            var ka :| a == n * ka;
            var kb :| b == n * kb;
            assert a + b == n * (ka + kb);                   // closure under +
        }
        forall a | L.In(a, s)
            ensures L.In(G.Inv(a), s)
        {
            var ka :| a == n * ka;
            assert -a == n * (-ka);                          // closure under negation
        }
    }

    // The even integers, 2Z.
    lemma EvensSubgroup()
        ensures IsSubgroup(iset x: int | exists k :: x == 2 * k)
    {
        MultiplesSubgroup(2);
    }

    // The whole group Z.
    lemma WholeIntSubgroup()
        ensures IsSubgroup(iset x: int | true)
    {
    }
}

// A genuinely finite group: the Klein four-group V = (Z/2)^2. Every element is
// its own inverse. All laws verify by exhaustive case analysis (no arithmetic).
module KleinFour refines AbelianGroup {
    datatype V = E | A | B | C
    type T = V

    function op(a: T, b: T): T {
        match a
        case E => b
        case A => (match b case E => A case A => E case B => C case C => B)
        case B => (match b case E => B case A => C case B => E case C => A)
        case C => (match b case E => C case A => B case B => A case C => E)
    }
    function Id(): T { E }
    function Inv(a: T): T { a }   // self-inverse

    lemma Assoc(a: T, b: T, c: T) {}
    lemma LeftId(a: T) {}
    lemma RightId(a: T) {}
    lemma LeftInv(a: T) {}
    lemma RightInv(a: T) {}
    lemma Comm(a: T, b: T) {}
}

// Finite subgroups of the Klein four-group, as ordinary sets.
module KleinSubgroups refines Subgroups {
    import G = KleinFour
    import L = SetColl

    // The three order-2 subgroups {E, X}.
    lemma SubgroupEA()
        ensures IsSubgroup({G.E, G.A})
    {
        forall a, b | L.In(a, {G.E, G.A}) && L.In(b, {G.E, G.A})
            ensures L.In(G.op(a, b), {G.E, G.A}) {}
        forall a | L.In(a, {G.E, G.A}) ensures L.In(G.Inv(a), {G.E, G.A}) {}
    }

    lemma SubgroupEB()
        ensures IsSubgroup({G.E, G.B})
    {
        forall a, b | L.In(a, {G.E, G.B}) && L.In(b, {G.E, G.B})
            ensures L.In(G.op(a, b), {G.E, G.B}) {}
        forall a | L.In(a, {G.E, G.B}) ensures L.In(G.Inv(a), {G.E, G.B}) {}
    }

    lemma SubgroupEC()
        ensures IsSubgroup({G.E, G.C})
    {
        forall a, b | L.In(a, {G.E, G.C}) && L.In(b, {G.E, G.C})
            ensures L.In(G.op(a, b), {G.E, G.C}) {}
        forall a | L.In(a, {G.E, G.C}) ensures L.In(G.Inv(a), {G.E, G.C}) {}
    }

    // The whole group {E, A, B, C}.
    lemma WholeKlein()
        ensures IsSubgroup({G.E, G.A, G.B, G.C})
    {
        forall a, b | L.In(a, {G.E, G.A, G.B, G.C}) && L.In(b, {G.E, G.A, G.B, G.C})
            ensures L.In(G.op(a, b), {G.E, G.A, G.B, G.C}) {}
    }
}

// Z/12Z, a finite cyclic group under addition mod 12.
module ZMod12 refines AbelianGroup {
    type T = x: int | 0 <= x < 12
    function op(a: T, b: T): T { (a + b) % 12 }
    function Id(): T { 0 }
    function Inv(a: T): T { (12 - a) % 12 }

    lemma Assoc(a: T, b: T, c: T) {}
    lemma LeftId(a: T) {}
    lemma RightId(a: T) {}
    lemma LeftInv(a: T) {}
    lemma RightInv(a: T) {}
    lemma Comm(a: T, b: T) {}
}

// Subgroups of Z/12Z. Each n-multiple set is a subgroup; e.g. {0,3,6,9} has
// order 4 and is isomorphic to Z/4Z, {0,4,8} has order 3 (= Z/3Z), {0,6} order 2.
module ZMod12Subgroups refines Subgroups {
    import G = ZMod12
    import L = SetColl

    // {0, 3, 6, 9}: order 4, isomorphic to Z/4Z.
    lemma SubgroupZ4()
        ensures IsSubgroup({0, 3, 6, 9})
    {
        forall a, b | L.In(a, {0, 3, 6, 9}) && L.In(b, {0, 3, 6, 9})
            ensures L.In(G.op(a, b), {0, 3, 6, 9}) {}
        forall a | L.In(a, {0, 3, 6, 9}) ensures L.In(G.Inv(a), {0, 3, 6, 9}) {}
    }

    // {0, 4, 8}: order 3, isomorphic to Z/3Z.
    lemma SubgroupZ3()
        ensures IsSubgroup({0, 4, 8})
    {
        forall a, b | L.In(a, {0, 4, 8}) && L.In(b, {0, 4, 8})
            ensures L.In(G.op(a, b), {0, 4, 8}) {}
        forall a | L.In(a, {0, 4, 8}) ensures L.In(G.Inv(a), {0, 4, 8}) {}
    }

    // {0, 6}: order 2, isomorphic to Z/2Z.
    lemma SubgroupZ2()
        ensures IsSubgroup({0, 6})
    {
        forall a, b | L.In(a, {0, 6}) && L.In(b, {0, 6})
            ensures L.In(G.op(a, b), {0, 6}) {}
        forall a | L.In(a, {0, 6}) ensures L.In(G.Inv(a), {0, 6}) {}
    }
}

// Z/4Z, the cyclic group of order 4.
module ZMod4 refines AbelianGroup {
    type T = x: int | 0 <= x < 4
    function op(a: T, b: T): T { (a + b) % 4 }
    function Id(): T { 0 }
    function Inv(a: T): T { (4 - a) % 4 }

    lemma Assoc(a: T, b: T, c: T) {}
    lemma LeftId(a: T) {}
    lemma RightId(a: T) {}
    lemma LeftInv(a: T) {}
    lemma RightInv(a: T) {}
    lemma Comm(a: T, b: T) {}
}

// A group homomorphism F : G -> H — a map preserving the operation (HomLaw). That
// single law forces F to preserve the identity and inverses too, proved here once
// for every instantiation.
abstract module GroupHom {
    import G : Group
    import H : Group

    function F(a: G.T): H.T

    lemma HomLaw(a: G.T, b: G.T)
        ensures F(G.op(a, b)) == H.op(F(a), F(b))

    ghost predicate Injective() {
        forall a: G.T, b: G.T :: F(a) == F(b) ==> a == b
    }

    // F(e_G) = e_H : F(e) = F(e.e) = F(e).F(e), then cancel.
    lemma FId()
        ensures F(G.Id()) == H.Id()
    {
        HomLaw(G.Id(), G.Id());
        G.LeftId(G.Id());                             // op(e,e) == e, so F(e) == F(e).F(e)
        H.RightId(F(G.Id()));                         // h.e == h
        H.LeftCancel(F(G.Id()), H.Id(), F(G.Id()));   // h.e == h.h  ==>  e == h
    }

    // F(a^-1) = F(a)^-1 : F(a).F(a^-1) = F(a.a^-1) = F(e) = e.
    lemma FInv(a: G.T)
        ensures F(G.Inv(a)) == H.Inv(F(a))
    {
        HomLaw(a, G.Inv(a));
        G.RightInv(a);                                // a.a^-1 == e
        FId();                                        // F(e) == e
        H.InvUniqueRight(F(a), F(G.Inv(a)));          // F(a).F(a^-1) == e ==> F(a^-1) == F(a)^-1
    }
}

// The isomorphism Z/4Z ~= {0,3,6,9} <= Z/12Z, realized by k |-> 3k mod 12.
module Z4toZ12 refines GroupHom {
    import G = ZMod4
    import H = ZMod12

    function F(a: G.T): H.T { (3 * a) % 12 }

    // F preserves +: 3*((a+b) mod 4) == (3a + 3b) mod 12, since 3s = 12*(s/4) + 3*(s mod 4).
    lemma HomLaw(a: G.T, b: G.T)
    {
        var s := a + b;
        assert 3 * a < 12 && 3 * b < 12;
        assert H.op(F(a), F(b)) == (3 * s) % 12;
        assert 0 <= s % 4 && 3 * (s % 4) < 12;
        assert F(G.op(a, b)) == 3 * (s % 4);
        assert 3 * s == 12 * (s / 4) + 3 * (s % 4);   // div/mod identity, scaled by 3
        assert (3 * s) % 12 == 3 * (s % 4);           // the 12*(s/4) term vanishes mod 12
    }

    // F is injective: 3a = 3b (both < 12) forces a = b.
    lemma IsInjective()
        ensures Injective()
    {
        forall a: G.T, b: G.T | F(a) == F(b)
            ensures a == b
        {
            assert F(a) == 3 * a && F(b) == 3 * b;
            assert a == b;
        }
    }

    // The image of F is exactly the order-4 subgroup {0,3,6,9}: the first ensures
    // gives image <= {0,3,6,9}, and F(0..3) = 0,3,6,9 gives {0,3,6,9} <= image.
    lemma ImageIsSubgroup()
        ensures forall a: G.T :: F(a) in {0, 3, 6, 9}
        ensures F(0) == 0 && F(1) == 3 && F(2) == 6 && F(3) == 9
    {
        forall a: G.T ensures F(a) in {0, 3, 6, 9} {
            assert F(a) == 3 * a;
            assert a == 0 || a == 1 || a == 2 || a == 3;
        }
    }
}
