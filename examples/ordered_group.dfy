include "../src/algebra.dfy"

// EXAMPLE: an ORDERED ABELIAN GROUP -- one carrier that is simultaneously TWO of
// the structures this library defines:
//
//   (1) an AbelianGroup  (src/algebra.dfy)   -- REFINED here, so we inherit op/Id/
//       Inv and ALL of its derived lemmas (InvId, InvInv, cancellation, ...);
//   (2) a total order    (the TotalOrder interface of src/orders.dfy)  -- INLINED
//       here (Leq + Refl/Antisym/Trans/Total), because Dafny modules have single
//       refinement. This is the very same trick the library's `Ring` uses: it
//       refines the additive AbelianGroup and inlines its multiplicative monoid.
//
// The two structures are independent until a single COMPATIBILITY AXIOM ties them
// together: the order is translation-invariant. From that one bridge, the group
// and the order genuinely interact, and the lemmas below are proved using laws
// from BOTH structures at once.
abstract module OrderedAbelianGroup refines AbelianGroup {
    // ---- the total-order interface (cf. Preorder..TotalOrder in src/orders.dfy) ----
    predicate Leq(a: T, b: T)
    lemma Refl(a: T)
        ensures Leq(a, a)
    lemma Antisym(a: T, b: T)
        requires Leq(a, b) && Leq(b, a)
        ensures a == b
    lemma Trans(a: T, b: T, c: T)
        requires Leq(a, b) && Leq(b, c)
        ensures Leq(a, c)
    lemma Total(a: T, b: T)
        ensures Leq(a, b) || Leq(b, a)

    ghost predicate Lt(a: T, b: T) { Leq(a, b) && a != b }

    // ---- the compatibility axiom linking the two structures ----
    // Left-translation preserves the order: the group acts by order-automorphisms.
    lemma TransInvariant(a: T, b: T, c: T)
        requires Leq(a, b)
        ensures Leq(op(c, a), op(c, b))

    // A pure group fact used throughout: a left translation by c is undone by Inv(c).
    lemma CancelLeft(c: T, x: T)
        ensures op(Inv(c), op(c, x)) == x
    {
        Assoc(Inv(c), c, x);   // op(Inv(c), op(c,x)) == op(op(Inv(c),c), x)
        LeftInv(c);            // op(Inv(c), c) == Id()
        LeftId(x);             // op(Id(), x) == x
    }

    // Translation is also order-REFLECTING (the converse of the axiom): the group
    // lets us undo the translation, so the implication runs both ways.
    lemma TransReflect(a: T, b: T, c: T)
        requires Leq(op(c, a), op(c, b))
        ensures Leq(a, b)
    {
        TransInvariant(op(c, a), op(c, b), Inv(c));   // Leq(op(Inv c, op(c,a)), op(Inv c, op(c,b)))
        CancelLeft(c, a);                              // op(Inv c, op(c,a)) == a
        CancelLeft(c, b);                              // op(Inv c, op(c,b)) == b
    }

    // The order is determined by the group "difference": a <= b iff -a + b >= 0.
    // The bridge between the order relation and the group's identity and inverse.
    lemma OrderIffNonnegDifference(a: T, b: T)
        ensures Leq(a, b) <==> Leq(Id(), op(Inv(a), b))
    {
        if Leq(a, b) {
            TransInvariant(a, b, Inv(a));   // Leq(op(Inv a, a), op(Inv a, b))
            LeftInv(a);                     // op(Inv a, a) == Id()
        }
        if Leq(Id(), op(Inv(a), b)) {
            TransInvariant(Id(), op(Inv(a), b), a);   // Leq(op(a, Id()), op(a, op(Inv a, b)))
            RightId(a);                                // op(a, Id()) == a
            calc {                                     // op(a, op(Inv a, b)) == b
                op(a, op(Inv(a), b));
                { Assoc(a, Inv(a), b); }
                op(op(a, Inv(a)), b);
                { RightInv(a); }
                op(Id(), b);
                { LeftId(b); }
                b;
            }
        }
    }

    // Negation REVERSES the order:  a <= b  ==>  -b <= -a.
    // Uses the compatibility axiom (TransInvariant) together with the group axioms
    // LeftInv / RightId / Comm / Assoc / LeftId.
    lemma InvReversesOrder(a: T, b: T)
        requires Leq(a, b)
        ensures Leq(Inv(b), Inv(a))
    {
        TransInvariant(a, b, Inv(a));   // Leq(op(Inv a, a), op(Inv a, b)) == Leq(Id(), op(Inv a, b))
        LeftInv(a);
        TransInvariant(Id(), op(Inv(a), b), Inv(b));   // Leq(op(Inv b, Id()), op(Inv b, op(Inv a, b)))
        RightId(Inv(b));                                // op(Inv b, Id()) == Inv b
        calc {                                          // op(Inv b, op(Inv a, b)) == Inv a
            op(Inv(b), op(Inv(a), b));
            { Comm(Inv(a), b); }
            op(Inv(b), op(b, Inv(a)));
            { Assoc(Inv(b), b, Inv(a)); }
            op(op(Inv(b), b), Inv(a));
            { LeftInv(b); }
            op(Id(), Inv(a));
            { LeftId(Inv(a)); }
            Inv(a);
        }
    }

    // Strict version:  a < b  ==>  -b < -a.  The Leq part is above; the STRICT part
    // (a != b ==> Inv b != Inv a) needs a DERIVED AbelianGroup lemma -- InvInv --
    // to push the equality back through negation.
    lemma StrictInvReverses(a: T, b: T)
        requires Lt(a, b)
        ensures Lt(Inv(b), Inv(a))
    {
        InvReversesOrder(a, b);     // Leq(Inv b, Inv a)
        if Inv(b) == Inv(a) {
            InvInv(a);              // a == Inv(Inv a)
            InvInv(b);              // b == Inv(Inv b) == Inv(Inv a) == a, contradicting a != b
        }
    }

    // Sign dichotomy: every element is >= 0 or its inverse is >= 0. This is where
    // an ORDER axiom (Total) and a GROUP-derived lemma (InvId) meet head-on,
    // through the combined InvReversesOrder.
    lemma SignDichotomy(a: T)
        ensures Leq(Id(), a) || Leq(Id(), Inv(a))
    {
        Total(a, Id());                  // order: Leq(a, Id()) || Leq(Id(), a)
        if Leq(a, Id()) {
            InvReversesOrder(a, Id());   // Leq(Inv(Id()), Inv a)
            InvId();                     // group-derived: Inv(Id()) == Id()
        }
    }
}

// The integers are an ordered abelian group: (Z, +, 0, -) with the usual <=. Every
// law -- group, order, and the translation-invariance bridge -- holds by integer
// arithmetic, so all instance obligations discharge with empty bodies.
module IntOrderedGroup refines OrderedAbelianGroup {
    type T = int
    function op(a: T, b: T): T { a + b }
    function Id(): T { 0 }
    function Inv(a: T): T { -a }
    predicate Leq(a: T, b: T) { a <= b }

    lemma Assoc(a: T, b: T, c: T) {}
    lemma LeftId(a: T) {}
    lemma RightId(a: T) {}
    lemma LeftInv(a: T) {}
    lemma RightInv(a: T) {}
    lemma Comm(a: T, b: T) {}
    lemma Refl(a: T) {}
    lemma Antisym(a: T, b: T) {}
    lemma Trans(a: T, b: T, c: T) {}
    lemma Total(a: T, b: T) {}
    lemma TransInvariant(a: T, b: T, c: T) {}
}

// A small demonstration: the ABSTRACT lemmas, proved once from the two structures'
// laws, specialize to concrete facts about the integers.
module OrderedGroupDemo {
    import IOG = IntOrderedGroup

    @Test
    method test() {
        // 3 <= 5, so by InvReversesOrder (negation reverses order), -5 <= -3.
        IOG.InvReversesOrder(3, 5);
        assert IOG.Leq(-5, -3);

        // 3 < 5, so strictly -5 < -3.
        IOG.StrictInvReverses(3, 5);
        assert IOG.Lt(-5, -3);

        // -4 is negative, so its inverse 4 is non-negative (sign dichotomy).
        IOG.SignDichotomy(-4);
        assert IOG.Leq(0, -4) || IOG.Leq(0, 4);

        print "InvReversesOrder(3,5):   -5 <= -3  is ", IOG.Leq(-5, -3), "\n";
        print "OrderIffNonnegDifference holds; SignDichotomy holds.\n";
    }
}
