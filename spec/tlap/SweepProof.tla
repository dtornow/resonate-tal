---------------------------- MODULE SweepProof ---------------------------
EXTENDS Refinement, NaturalsInduction, TLAPS

D1(o, b, t) == P!Due1(o, b, t)

Fl(S) == P!Flat(S)

F(base, box, t, bound) ==
    LET R[k \in 0 .. bound] ==
            IF k = 0 THEN
                {[objects |-> base, outbox |-> box]}
            ELSE
                LET prev == R[k - 1]
                IN  prev \cup Fl({ D1(st.objects, st.outbox, t) : st \in prev })
    IN  R

LEMMA Unfold ==
    ASSUME NEW base, NEW box, NEW t, NEW bound \in Nat
    PROVE  F(base, box, t, bound)
              = [ k \in 0 .. bound |->
                    IF k = 0 THEN {[objects |-> base, outbox |-> box]}
                    ELSE F(base, box, t, bound)[k - 1]
                           \cup Fl({ D1(st.objects, st.outbox, t) :
                                       st \in F(base, box, t, bound)[k - 1] }) ]
PROOF
    <1> DEFINE Def(prev, k) ==
                   prev \cup Fl({ D1(st.objects, st.outbox, t) : st \in prev })
    <1> DEFINE f == F(base, box, t, bound)
    <1> DEFINE c == {[objects |-> base, outbox |-> box]}
    <1>1. FiniteNatInductiveDefHypothesis(f, c, Def, 0, bound)
        BY DEF f, c, Def, F, FiniteNatInductiveDefHypothesis
    <1>2. FiniteNatInductiveDefConclusion(f, c, Def, 0, bound)
        BY <1>1, FiniteNatInductiveDef
    <1>3. QED
        BY <1>2 DEF FiniteNatInductiveDefConclusion, f, c, Def, Fl, D1, P!Flat, P!Due1

LEMMA AtZero ==
    ASSUME NEW base, NEW box, NEW t, NEW bound \in Nat
    PROVE  F(base, box, t, bound)[0] = {[objects |-> base, outbox |-> box]}
PROOF
    BY Unfold, Z3

LEMMA AtNext ==
    ASSUME NEW base, NEW box, NEW t, NEW bound \in Nat, NEW k \in 1 .. bound
    PROVE  F(base, box, t, bound)[k]
              =   F(base, box, t, bound)[k - 1]
                \cup Fl({ D1(st.objects, st.outbox, t) :
                            st \in F(base, box, t, bound)[k - 1] })
PROOF
    BY Unfold, Z3

Prefix(chain, k) ==
    [i \in 0 .. k |-> chain[i]]

InStage(base, box, t, bound, chain, k) ==
    Prefix(chain, k)[k] \in F(base, box, t, bound)[k]

LEMMA ChainIn ==
    ASSUME NEW base, NEW box, NEW t, NEW bound \in Nat,
           NEW n \in 0 .. bound, NEW chain,
           DOMAIN chain = 0 .. n,
           chain[0] = [objects |-> base, outbox |-> box],
           \A i \in 0 .. (n - 1) :
              chain[i + 1] \in D1(chain[i].objects, chain[i].outbox, t)
    PROVE  chain[n] \in F(base, box, t, bound)[n]
PROOF
    <1> DEFINE Held(k) == k \in 0 .. n => InStage(base, box, t, bound, chain, k)
    <1>1. Held(0)
        BY AtZero, Z3 DEF Held, InStage, Prefix
    <1>2. ASSUME NEW k \in Nat, Held(k)
          PROVE  Held(k + 1)
        <2>1. CASE k + 1 \notin 0 .. n
            BY <2>1 DEF Held
        <2>2. CASE k + 1 \in 0 .. n
            <3>1. k \in 0 .. n /\ k \in Nat
                BY <2>2, Z3
            <3>2. Prefix(chain, k)[k] \in F(base, box, t, bound)[k]
                BY <1>2, <3>1 DEF Held, InStage
            <3>3. F(base, box, t, bound)[k + 1]
                    =   F(base, box, t, bound)[k]
                      \cup Fl({ D1(st.objects, st.outbox, t) :
                                  st \in F(base, box, t, bound)[k] })
                BY <2>2, <3>1, AtNext, Z3
            <3>4. chain[k + 1] \in D1(chain[k].objects, chain[k].outbox, t)
                BY <2>2, <3>1, Z3
            <3>5. Prefix(chain, k + 1)[k + 1] = chain[k + 1]
                    /\ Prefix(chain, k)[k] = chain[k]
                BY Z3 DEF Prefix
            <3> DEFINE bundle ==
                    { D1(st.objects, st.outbox, t) :
                        st \in F(base, box, t, bound)[k] }
            <3>6. chain[k + 1] \in UNION bundle /\ bundle /= {}
                BY <3>2, <3>4, <3>5, Z3 DEF bundle
            <3>7. Fl(bundle) = UNION bundle
                BY <3>6 DEF Fl, P!Flat
            <3>8. Prefix(chain, k + 1)[k + 1] \in F(base, box, t, bound)[k + 1]
                BY <3>3, <3>5, <3>6, <3>7, Z3 DEF bundle
            <3>9. QED
                BY <2>2, <3>8 DEF Held, InStage
        <2>3. QED
            BY <2>1, <2>2
    <1>3. \A k \in Nat : Held(k) => Held(k + 1)
        BY <1>2
    <1>4. \A k \in Nat : Held(k)
        <2>1. HIDE DEF Held
        <2>2. QED
            BY <1>1, <1>3, NatInduction, Isa
    <1>5. Held(n)
        BY <1>4, Z3
    <1>6. QED
        BY <1>5 DEF Held, InStage, Prefix

===============================================================================
