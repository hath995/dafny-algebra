// An abstract collection (set) type, in the spirit of the Topology module: the
// concrete container (set vs iset) is itself abstract. Operations and their
// membership-characterization laws are declared abstractly; the derived set
// algebra (commutativity, associativity, distributivity, absorption, De Morgan)
// is proved ONCE from those, and inherited by the set and iset instantiations.
abstract module Collection {
    type C(!new)<A(==, !new)>

    ghost predicate In<A(!new)>(x: A, s: C<A>)
    ghost function Empty<A(!new)>(): C<A>
    ghost function Single<A(!new)>(x: A): C<A>
    ghost function Union<A(!new)>(s: C<A>, t: C<A>): C<A>
    ghost function Inter<A(!new)>(s: C<A>, t: C<A>): C<A>
    ghost function Diff<A(!new)>(s: C<A>, t: C<A>): C<A>
    ghost predicate Subset<A(!new)>(s: C<A>, t: C<A>)

    // ---- characterization laws (what each operation means, member-wise) ----
    lemma EmptyChar<A(!new)>(x: A)
        ensures !In(x, Empty<A>())
    lemma SingleChar<A(!new)>(y: A, x: A)
        ensures In(x, Single(y)) <==> x == y
    lemma UnionChar<A(!new)>(s: C<A>, t: C<A>, x: A)
        ensures In(x, Union(s, t)) <==> In(x, s) || In(x, t)
    lemma InterChar<A(!new)>(s: C<A>, t: C<A>, x: A)
        ensures In(x, Inter(s, t)) <==> In(x, s) && In(x, t)
    lemma DiffChar<A(!new)>(s: C<A>, t: C<A>, x: A)
        ensures In(x, Diff(s, t)) <==> In(x, s) && !In(x, t)
    lemma SubsetChar<A(!new)>(s: C<A>, t: C<A>)
        ensures Subset(s, t) <==> (forall x :: In(x, s) ==> In(x, t))
    lemma Extensionality<A(!new)>(s: C<A>, t: C<A>)
        requires forall x :: In(x, s) <==> In(x, t)
        ensures s == t

    // ---- derived set algebra (proved once from the laws above) ----
    lemma UnionComm<A(!new)>(s: C<A>, t: C<A>)
        ensures Union(s, t) == Union(t, s)
    {
        forall x ensures In(x, Union(s, t)) <==> In(x, Union(t, s)) {
            UnionChar(s, t, x); UnionChar(t, s, x);
        }
        Extensionality(Union(s, t), Union(t, s));
    }

    lemma InterComm<A(!new)>(s: C<A>, t: C<A>)
        ensures Inter(s, t) == Inter(t, s)
    {
        forall x ensures In(x, Inter(s, t)) <==> In(x, Inter(t, s)) {
            InterChar(s, t, x); InterChar(t, s, x);
        }
        Extensionality(Inter(s, t), Inter(t, s));
    }

    lemma UnionAssoc<A(!new)>(s: C<A>, t: C<A>, u: C<A>)
        ensures Union(Union(s, t), u) == Union(s, Union(t, u))
    {
        forall x ensures In(x, Union(Union(s, t), u)) <==> In(x, Union(s, Union(t, u))) {
            UnionChar(Union(s, t), u, x); UnionChar(s, t, x);
            UnionChar(s, Union(t, u), x); UnionChar(t, u, x);
        }
        Extensionality(Union(Union(s, t), u), Union(s, Union(t, u)));
    }

    lemma InterAssoc<A(!new)>(s: C<A>, t: C<A>, u: C<A>)
        ensures Inter(Inter(s, t), u) == Inter(s, Inter(t, u))
    {
        forall x ensures In(x, Inter(Inter(s, t), u)) <==> In(x, Inter(s, Inter(t, u))) {
            InterChar(Inter(s, t), u, x); InterChar(s, t, x);
            InterChar(s, Inter(t, u), x); InterChar(t, u, x);
        }
        Extensionality(Inter(Inter(s, t), u), Inter(s, Inter(t, u)));
    }

    lemma UnionIdem<A(!new)>(s: C<A>)
        ensures Union(s, s) == s
    {
        forall x ensures In(x, Union(s, s)) <==> In(x, s) { UnionChar(s, s, x); }
        Extensionality(Union(s, s), s);
    }

    lemma InterIdem<A(!new)>(s: C<A>)
        ensures Inter(s, s) == s
    {
        forall x ensures In(x, Inter(s, s)) <==> In(x, s) { InterChar(s, s, x); }
        Extensionality(Inter(s, s), s);
    }

    lemma UnionEmpty<A(!new)>(s: C<A>)   // Empty is the identity of Union
        ensures Union(s, Empty<A>()) == s
    {
        forall x ensures In(x, Union(s, Empty<A>())) <==> In(x, s) {
            UnionChar(s, Empty<A>(), x); EmptyChar(x);
        }
        Extensionality(Union(s, Empty<A>()), s);
    }

    lemma InterEmpty<A(!new)>(s: C<A>)   // Empty annihilates Inter
        ensures Inter(s, Empty<A>()) == Empty<A>()
    {
        forall x ensures In(x, Inter(s, Empty<A>())) <==> In(x, Empty<A>()) {
            InterChar(s, Empty<A>(), x); EmptyChar(x);
        }
        Extensionality(Inter(s, Empty<A>()), Empty<A>());
    }

    lemma UnionDistribInter<A(!new)>(s: C<A>, t: C<A>, u: C<A>)
        ensures Union(s, Inter(t, u)) == Inter(Union(s, t), Union(s, u))
    {
        forall x ensures In(x, Union(s, Inter(t, u))) <==> In(x, Inter(Union(s, t), Union(s, u))) {
            UnionChar(s, Inter(t, u), x); InterChar(t, u, x);
            InterChar(Union(s, t), Union(s, u), x); UnionChar(s, t, x); UnionChar(s, u, x);
        }
        Extensionality(Union(s, Inter(t, u)), Inter(Union(s, t), Union(s, u)));
    }

    lemma InterDistribUnion<A(!new)>(s: C<A>, t: C<A>, u: C<A>)
        ensures Inter(s, Union(t, u)) == Union(Inter(s, t), Inter(s, u))
    {
        forall x ensures In(x, Inter(s, Union(t, u))) <==> In(x, Union(Inter(s, t), Inter(s, u))) {
            InterChar(s, Union(t, u), x); UnionChar(t, u, x);
            UnionChar(Inter(s, t), Inter(s, u), x); InterChar(s, t, x); InterChar(s, u, x);
        }
        Extensionality(Inter(s, Union(t, u)), Union(Inter(s, t), Inter(s, u)));
    }

    lemma AbsorbUnion<A(!new)>(s: C<A>, t: C<A>)
        ensures Union(s, Inter(s, t)) == s
    {
        forall x ensures In(x, Union(s, Inter(s, t))) <==> In(x, s) {
            UnionChar(s, Inter(s, t), x); InterChar(s, t, x);
        }
        Extensionality(Union(s, Inter(s, t)), s);
    }

    lemma AbsorbInter<A(!new)>(s: C<A>, t: C<A>)
        ensures Inter(s, Union(s, t)) == s
    {
        forall x ensures In(x, Inter(s, Union(s, t))) <==> In(x, s) {
            InterChar(s, Union(s, t), x); UnionChar(s, t, x);
        }
        Extensionality(Inter(s, Union(s, t)), s);
    }

    // De Morgan, with Diff(u, -) as relative complement in u.
    lemma DeMorganUnion<A(!new)>(u: C<A>, s: C<A>, t: C<A>)
        ensures Diff(u, Union(s, t)) == Inter(Diff(u, s), Diff(u, t))
    {
        forall x ensures In(x, Diff(u, Union(s, t))) <==> In(x, Inter(Diff(u, s), Diff(u, t))) {
            DiffChar(u, Union(s, t), x); UnionChar(s, t, x);
            InterChar(Diff(u, s), Diff(u, t), x); DiffChar(u, s, x); DiffChar(u, t, x);
        }
        Extensionality(Diff(u, Union(s, t)), Inter(Diff(u, s), Diff(u, t)));
    }

    lemma DeMorganInter<A(!new)>(u: C<A>, s: C<A>, t: C<A>)
        ensures Diff(u, Inter(s, t)) == Union(Diff(u, s), Diff(u, t))
    {
        forall x ensures In(x, Diff(u, Inter(s, t))) <==> In(x, Union(Diff(u, s), Diff(u, t))) {
            DiffChar(u, Inter(s, t), x); InterChar(s, t, x);
            UnionChar(Diff(u, s), Diff(u, t), x); DiffChar(u, s, x); DiffChar(u, t, x);
        }
        Extensionality(Diff(u, Inter(s, t)), Union(Diff(u, s), Diff(u, t)));
    }
}

// Finite collections.
module SetColl refines Collection {
    type C<A(==, !new)> = set<A>
    ghost predicate In<A(!new)>(x: A, s: C<A>) { x in s }
    ghost function Empty<A(!new)>(): C<A> { {} }
    ghost function Single<A(!new)>(x: A): C<A> { {x} }
    ghost function Union<A(!new)>(s: C<A>, t: C<A>): C<A> { s + t }
    ghost function Inter<A(!new)>(s: C<A>, t: C<A>): C<A> { s * t }
    ghost function Diff<A(!new)>(s: C<A>, t: C<A>): C<A> { s - t }
    ghost predicate Subset<A(!new)>(s: C<A>, t: C<A>) { s <= t }

    lemma EmptyChar<A(!new)>(x: A) {}
    lemma SingleChar<A(!new)>(y: A, x: A) {}
    lemma UnionChar<A(!new)>(s: C<A>, t: C<A>, x: A) {}
    lemma InterChar<A(!new)>(s: C<A>, t: C<A>, x: A) {}
    lemma DiffChar<A(!new)>(s: C<A>, t: C<A>, x: A) {}
    lemma SubsetChar<A(!new)>(s: C<A>, t: C<A>) {
        forall x ensures In(x, s) <==> x in s {}
        forall x ensures In(x, t) <==> x in t {}
    }
    lemma Extensionality<A(!new)>(s: C<A>, t: C<A>) {
        forall x ensures x in s <==> x in t {
            assert In(x, s) <==> In(x, t);   // instantiate the requires; In unfolds to `in`
        }
    }
}

// Arbitrary (possibly infinite) collections.
module ISetColl refines Collection {
    type C<!A(==, !new)> = iset<A>
    ghost predicate In<A(!new)>(x: A, s: C<A>) { x in s }
    ghost function Empty<A(!new)>(): C<A> { iset{} }
    ghost function Single<A(!new)>(x: A): C<A> { iset{x} }
    ghost function Union<A(!new)>(s: C<A>, t: C<A>): C<A> { s + t }
    ghost function Inter<A(!new)>(s: C<A>, t: C<A>): C<A> { s * t }
    ghost function Diff<A(!new)>(s: C<A>, t: C<A>): C<A> { s - t }
    ghost predicate Subset<A(!new)>(s: C<A>, t: C<A>) { s <= t }

    lemma EmptyChar<A(!new)>(x: A) {}
    lemma SingleChar<A(!new)>(y: A, x: A) {}
    lemma UnionChar<A(!new)>(s: C<A>, t: C<A>, x: A) {}
    lemma InterChar<A(!new)>(s: C<A>, t: C<A>, x: A) {}
    lemma DiffChar<A(!new)>(s: C<A>, t: C<A>, x: A) {}
    lemma SubsetChar<A(!new)>(s: C<A>, t: C<A>) {
        forall x ensures In(x, s) <==> x in s {}
        forall x ensures In(x, t) <==> x in t {}
    }
    lemma Extensionality<A(!new)>(s: C<A>, t: C<A>) {
        forall x ensures x in s <==> x in t {
            assert In(x, s) <==> In(x, t);   // instantiate the requires; In unfolds to `in`
        }
    }
}
