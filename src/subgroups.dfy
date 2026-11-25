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
