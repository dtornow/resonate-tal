------------------------------ MODULE Reach -------------------------------
(* A due-action chain sits in the sweep closure, and the timeout pass is one
   such chain: each pending deadline is one promise step, in any order. *)
EXTENDS SweepProof, FiniteSetTheorems, TLAPS

AXIOM FiniteOrigin == IsFiniteSet(Origin)
AXIOM FiniteRest == IsFiniteSet(Rest)
AXIOM FiniteAddress == IsFiniteSet(Address)

LEMMA RecEq ==
    ASSUME NEW r \in Id
    PROVE  r = [origin |-> r.origin, rest |-> r.rest]
PROOF
    BY IsaT(90) DEF Id

LEMMA IdParts ==
    ASSUME NEW r \in Id
    PROVE  r.origin \in Origin /\ r.rest \in Rest
PROOF
    BY Z3 DEF Id

LEMMA PairIn ==
    ASSUME NEW S, NEW T, NEW a \in S, NEW b \in T
    PROVE  <<a, b>> \in S \X T
PROOF
    BY Z3

LEMMA IdFinite ==
    ASSUME IsFiniteSet(Origin), IsFiniteSet(Rest)
    PROVE  IsFiniteSet(Id)
PROOF
    <1> DEFINE Op(p) == [origin |-> p[1], rest |-> p[2]]
    <1> DEFINE Img == { Op(p) : p \in Origin \X Rest }
    <1>1. IsFiniteSet(Origin \X Rest)
        BY FS_Product
    <1>2. LET T == { Op(x) : x \in Origin \X Rest }
          IN  IsFiniteSet(T)
        BY <1>1, FS_Image
    <1>3. IsFiniteSet(Img)
        BY <1>2 DEF Img
    <1>4. Id \subseteq Img
        <2> SUFFICES ASSUME NEW r \in Id
                     PROVE  r \in Img
            OBVIOUS
        <2>1. r.origin \in Origin /\ r.rest \in Rest
            BY IdParts
        <2> DEFINE p == <<r.origin, r.rest>>
        <2>2. p \in Origin \X Rest
            BY <2>1, PairIn DEF p
        <2>3. r = Op(p)
            BY <2>2, RecEq, Isa DEF Op, p
        <2>4. QED
            BY <2>2, <2>3 DEF Img
    <1>5. QED
        BY <1>3, <1>4, FS_Subset

LEMMA SameId ==
    P!Id = Id
PROOF
    BY DEF P!Id, Id

LEMMA SameCard ==
    ASSUME NEW S
    PROVE  P!Cardinality(S) = Cardinality(S)
PROOF
    BY DEF P!Cardinality, Cardinality

LEMMA SweepCap ==
    /\ P!MaxSweep \in Nat
    /\ Cardinality(Id) <= P!MaxSweep
PROOF
    <1>1. IsFiniteSet(Id) /\ Cardinality(Id) \in Nat
        BY FiniteOrigin, FiniteRest, IdFinite, FS_CardinalityType
    <1>2. Cardinality(Address) \in Nat
        BY FiniteAddress, FS_CardinalityType
    <1>3. /\ P!Cardinality(P!Id) = Cardinality(Id)
          /\ P!Cardinality(Address) = Cardinality(Address)
        BY SameId, SameCard
    <1>4. P!MaxSweep
            = Cardinality(Id)
              * (Cardinality(Id) + Cardinality(Address) + 3)
        BY <1>3 DEF P!MaxSweep
    <1>5. QED
        BY <1>1, <1>2, <1>4, Z3

G(base, box, t, bound) ==
    LET R[k \in 0 .. bound] ==
            IF k = 0 THEN
                {[objects |-> base, outbox |-> box]}
            ELSE
                LET prev == R[k - 1]
                IN  prev \cup P!Flat({ P!Due1(st.objects, st.outbox, t) : st \in prev })
    IN  R

LEMMA UnfoldG ==
    ASSUME NEW base, NEW box, NEW t, NEW bound \in Nat
    PROVE  G(base, box, t, bound)
              = [ k \in 0 .. bound |->
                    IF k = 0 THEN {[objects |-> base, outbox |-> box]}
                    ELSE G(base, box, t, bound)[k - 1]
                           \cup P!Flat({ P!Due1(st.objects, st.outbox, t) :
                                          st \in G(base, box, t, bound)[k - 1] }) ]
PROOF
    <1> DEFINE Def(prev, k) ==
                   prev \cup P!Flat({ P!Due1(st.objects, st.outbox, t) : st \in prev })
    <1> DEFINE f == G(base, box, t, bound)
    <1> DEFINE c == {[objects |-> base, outbox |-> box]}
    <1>1. FiniteNatInductiveDefHypothesis(f, c, Def, 0, bound)
        BY DEF f, c, Def, G, FiniteNatInductiveDefHypothesis
    <1>2. FiniteNatInductiveDefConclusion(f, c, Def, 0, bound)
        BY <1>1, FiniteNatInductiveDef
    <1>3. QED
        BY <1>2 DEF FiniteNatInductiveDefConclusion, f, c, Def

LEMMA AtZeroG ==
    ASSUME NEW base, NEW box, NEW t, NEW bound \in Nat
    PROVE  G(base, box, t, bound)[0] = {[objects |-> base, outbox |-> box]}
PROOF
    BY UnfoldG, Z3

LEMMA AtNextG ==
    ASSUME NEW base, NEW box, NEW t, NEW bound \in Nat, NEW k \in 1 .. bound
    PROVE  G(base, box, t, bound)[k]
              =   G(base, box, t, bound)[k - 1]
                \cup P!Flat({ P!Due1(st.objects, st.outbox, t) :
                                st \in G(base, box, t, bound)[k - 1] })
PROOF
    BY UnfoldG, Z3

LEMMA SameFG ==
    ASSUME NEW base, NEW box, NEW t, NEW bound \in Nat
    PROVE  \A k \in 0 .. bound :
              F(base, box, t, bound)[k] = G(base, box, t, bound)[k]
PROOF
    <1> DEFINE Eq(k) ==
            k \in 0 .. bound =>
                F(base, box, t, bound)[k] = G(base, box, t, bound)[k]
    <1>1. Eq(0)
        <2>1. F(base, box, t, bound)[0] = {[objects |-> base, outbox |-> box]}
            BY AtZero
        <2>2. G(base, box, t, bound)[0] = {[objects |-> base, outbox |-> box]}
            BY AtZeroG
        <2>3. QED
            BY <2>1, <2>2, Isa DEF Eq
    <1>2. ASSUME NEW k \in Nat, Eq(k)
          PROVE  Eq(k + 1)
        <2>1. CASE k + 1 \notin 0 .. bound
            BY <2>1 DEF Eq
        <2>2. CASE k + 1 \in 0 .. bound
            <3>1. k \in 0 .. bound /\ k + 1 \in 1 .. bound
                BY <2>2, Z3
            <3>2. F(base, box, t, bound)[k] = G(base, box, t, bound)[k]
                BY <1>2, <3>1 DEF Eq
            <3>3. F(base, box, t, bound)[k + 1]
                    =   F(base, box, t, bound)[k]
                      \cup Fl({ D1(st.objects, st.outbox, t) :
                                  st \in F(base, box, t, bound)[k] })
                BY <3>1, AtNext, Z3
            <3>4. G(base, box, t, bound)[k + 1]
                    =   G(base, box, t, bound)[k]
                      \cup P!Flat({ P!Due1(st.objects, st.outbox, t) :
                                      st \in G(base, box, t, bound)[k] })
                BY <3>1, AtNextG, Z3
            <3>5. QED
                BY <2>2, <3>2, <3>3, <3>4, Z3 DEF Eq, Fl, D1, P!Flat, P!Due1
        <2>3. QED
            BY <2>1, <2>2
    <1>3. \A k \in Nat : Eq(k) => Eq(k + 1)
        BY <1>2
    <1>4. \A k \in Nat : Eq(k)
        <2>1. HIDE DEF Eq
        <2>2. QED
            BY <1>1, <1>3, NatInduction, Isa
    <1>5. QED
        BY <1>4 DEF Eq

LEMMA SweptIs ==
    ASSUME NEW t
    PROVE  P!Swept(t) = F(Objects, outbox, t, P!MaxSweep)[P!MaxSweep]
PROOF
    <1>1. P!MaxSweep \in Nat
        BY SweepCap
    <1>2. F(Objects, outbox, t, P!MaxSweep)[P!MaxSweep]
            = G(Objects, outbox, t, P!MaxSweep)[P!MaxSweep]
        BY <1>1, SameFG
    <1>3. G(Objects, outbox, t, P!MaxSweep)[P!MaxSweep] = P!Swept(t)
        BY DEF G, P!Swept, P!MaxSweep
    <1>4. QED
        BY <1>2, <1>3

LEMMA Grows ==
    ASSUME NEW base, NEW box, NEW t, NEW bound \in Nat,
           NEW k \in 0 .. (bound - 1)
    PROVE  F(base, box, t, bound)[k] \subseteq F(base, box, t, bound)[k + 1]
PROOF
    <1>1. k + 1 \in 1 .. bound
        BY Z3
    <1>2. F(base, box, t, bound)[k + 1]
            =   F(base, box, t, bound)[k]
              \cup Fl({ D1(st.objects, st.outbox, t) :
                          st \in F(base, box, t, bound)[k] })
        BY <1>1, AtNext
    <1>3. QED
        BY <1>2, Z3

LEMMA Later ==
    ASSUME NEW base, NEW box, NEW t, NEW bound \in Nat, NEW n \in 0 .. bound
    PROVE  \A m \in n .. bound :
              F(base, box, t, bound)[n] \subseteq F(base, box, t, bound)[m]
PROOF
    <1> DEFINE Held(k) ==
            k \in n .. bound =>
                F(base, box, t, bound)[n] \subseteq F(base, box, t, bound)[k]
    <1>1. Held(0)
        BY Z3 DEF Held
    <1>2. ASSUME NEW k \in Nat, Held(k)
          PROVE  Held(k + 1)
        <2>1. CASE k + 1 \notin n .. bound
            BY <2>1 DEF Held
        <2>2. CASE k + 1 \in n .. bound /\ k + 1 = n
            BY <2>2, Z3 DEF Held
        <2>3. CASE k + 1 \in n .. bound /\ k + 1 # n
            <3>1. k \in n .. bound /\ k \in 0 .. (bound - 1)
                BY <2>3, Z3
            <3>2. F(base, box, t, bound)[n] \subseteq F(base, box, t, bound)[k]
                BY <1>2, <3>1 DEF Held
            <3>3. F(base, box, t, bound)[k] \subseteq F(base, box, t, bound)[k + 1]
                BY <3>1, Grows
            <3>4. QED
                BY <2>3, <3>2, <3>3, Z3 DEF Held
        <2>4. QED
            BY <2>1, <2>2, <2>3, Z3
    <1>3. \A k \in Nat : Held(k) => Held(k + 1)
        BY <1>2
    <1>4. \A k \in Nat : Held(k)
        <2>1. HIDE DEF Held
        <2>2. QED
            BY <1>1, <1>3, NatInduction, Isa
    <1>5. QED
        BY <1>4 DEF Held

Store(os, b) ==
    [objects |-> os, outbox |-> b]

StepOk(chain, t, n) ==
    /\ DOMAIN chain = 0 .. n
    /\ \A i \in 0 .. (n - 1) :
          chain[i + 1] \in D1(chain[i].objects, chain[i].outbox, t)

ReachN(base, box, t, os, b, n) ==
    \E chain :
        /\ chain[0] = Store(base, box)
        /\ StepOk(chain, t, n)
        /\ chain[n] = Store(os, b)

LEMMA ReachZero ==
    ASSUME NEW base, NEW box, NEW t
    PROVE  ReachN(base, box, t, base, box, 0)
PROOF
    <1> DEFINE chain == [i \in 0 .. 0 |-> Store(base, box)]
    <1>1. /\ chain[0] = Store(base, box)
          /\ StepOk(chain, t, 0)
          /\ chain[0] = Store(base, box)
        BY Z3 DEF chain, StepOk, Store
    <1>2. QED
        BY <1>1 DEF ReachN

LEMMA ReachAppend ==
    ASSUME NEW base, NEW box, NEW t, NEW os, NEW b, NEW os2, NEW b2,
           NEW n \in Nat,
           ReachN(base, box, t, os, b, n),
           Store(os2, b2) \in D1(os, b, t)
    PROVE  ReachN(base, box, t, os2, b2, n + 1)
PROOF
    <1>1. PICK chain :
            /\ chain[0] = Store(base, box)
            /\ StepOk(chain, t, n)
            /\ chain[n] = Store(os, b)
        BY DEF ReachN
    <1> DEFINE chain2 ==
            [i \in 0 .. (n + 1) |->
                IF i = n + 1 THEN Store(os2, b2) ELSE chain[i]]
    <1>2. chain2[0] = Store(base, box) /\ chain2[n + 1] = Store(os2, b2)
        BY <1>1, Z3 DEF chain2
    <1>3. StepOk(chain2, t, n + 1)
        <2>1. DOMAIN chain2 = 0 .. (n + 1)
            BY Z3 DEF chain2
        <2>2. ASSUME NEW i \in 0 .. n
              PROVE  chain2[i + 1] \in D1(chain2[i].objects, chain2[i].outbox, t)
            <3>1. CASE i < n
                BY <1>1, <2>2, <3>1, Z3 DEF chain2, StepOk
            <3>2. CASE i = n
                BY <1>1, <2>2, <3>2, Z3 DEF chain2, Store
            <3>3. QED
                BY <2>2, <3>1, <3>2, Z3
        <2>3. QED
            BY <2>1, <2>2 DEF StepOk
    <1>4. QED
        BY <1>2, <1>3 DEF ReachN

LEMMA ReachIn ==
    ASSUME NEW base, NEW box, NEW t, NEW os, NEW b,
           NEW n \in 0 .. P!MaxSweep,
           ReachN(base, box, t, os, b, n)
    PROVE  Store(os, b) \in F(base, box, t, P!MaxSweep)[P!MaxSweep]
PROOF
    <1>1. P!MaxSweep \in Nat
        BY SweepCap
    <1>2. PICK chain :
            /\ chain[0] = Store(base, box)
            /\ StepOk(chain, t, n)
            /\ chain[n] = Store(os, b)
        BY DEF ReachN
    <1>3. chain[n] \in F(base, box, t, P!MaxSweep)[n]
        BY <1>1, <1>2, ChainIn DEF Store, StepOk
    <1>4. F(base, box, t, P!MaxSweep)[n]
            \subseteq F(base, box, t, P!MaxSweep)[P!MaxSweep]
        BY <1>1, Later
    <1>5. QED
        BY <1>2, <1>3, <1>4

DueP(o, t) ==
    { j \in DOMAIN o :
        o[j].promise.state = "pending" /\ o[j].promise.timeoutAt <= t }

BulkP(o, T, t) ==
    [ i \in DOMAIN o |-> IF i \in T THEN P!Project(o[i], t) ELSE o[i] ]

Image(o, T, t) ==
    IF T = {} THEN o ELSE BulkP(o, T, t)

LEMMA DueSubset ==
    ASSUME NEW o, NEW t
    PROVE  DueP(o, t) \subseteq DOMAIN o
PROOF
    BY DEF DueP

LEMMA DueBound ==
    ASSUME NEW base, NEW t, DOMAIN base \subseteq Id
    PROVE  /\ IsFiniteSet(DueP(base, t))
           /\ Cardinality(DueP(base, t)) \in 0 .. P!MaxSweep
PROOF
    <1>1. DueP(base, t) \subseteq Id
        BY DueSubset, Z3
    <1>2. IsFiniteSet(Id) /\ Cardinality(Id) <= P!MaxSweep /\ P!MaxSweep \in Nat
        BY FiniteOrigin, FiniteRest, IdFinite, SweepCap
    <1>3. /\ IsFiniteSet(DueP(base, t))
          /\ Cardinality(DueP(base, t)) <= Cardinality(Id)
        BY <1>1, <1>2, FS_Subset
    <1>4. Cardinality(Id) \in Nat /\ Cardinality(DueP(base, t)) \in Nat
        BY <1>2, <1>3, FS_CardinalityType
    <1>5. QED
        BY <1>2, <1>3, <1>4, Z3

LEMMA ExtCtor ==
    ASSUME NEW S, NEW T, NEW e(_), NEW g(_),
           S = T,
           \A x \in S : e(x) = g(x)
    PROVE  [x \in S |-> e(x)] = [x \in T |-> g(x)]
PROOF
    BY Isa

LEMMA DomCtor ==
    ASSUME NEW S, NEW e(_)
    PROVE  DOMAIN [x \in S |-> e(x)] = S
PROOF
    BY Z3

LEMMA DuePromiseMember ==
    ASSUME NEW o, NEW b, NEW t, NEW i \in DOMAIN o,
           o[i].promise.state = "pending",
           o[i].promise.timeoutAt <= t
    PROVE  Store(P!Write(o, i, P!Project(o[i], t)), b) \in P!DuePromise(o, b, t)
PROOF
    BY DEF Store, P!DuePromise, P!Project, P!Write

LEMMA InDue1 ==
    ASSUME NEW o, NEW b, NEW t, NEW st \in P!DuePromise(o, b, t)
    PROVE  st \in D1(o, b, t)
PROOF
    BY DEF D1, P!Due1

LEMMA ImageAt ==
    ASSUME NEW o, NEW t, NEW T, NEW x,
           x \in DOMAIN o, x \notin T, T \subseteq DOMAIN o
    PROVE  /\ x \in DOMAIN Image(o, T, t)
           /\ Image(o, T, t)[x] = o[x]
PROOF
    <1>1. CASE T = {}
        BY <1>1 DEF Image
    <1>2. CASE T # {}
        <2>1. Image(o, T, t) = BulkP(o, T, t)
            BY <1>2 DEF Image
        <2>2. DOMAIN BulkP(o, T, t) = DOMAIN o
            BY DomCtor DEF BulkP
        <2>3. QED
            BY <1>2, <2>1, <2>2, Z3 DEF BulkP
    <1>3. QED
        BY <1>1, <1>2

LEMMA WriteBulk ==
    ASSUME NEW o, NEW t, NEW T, NEW x,
           x \in DOMAIN o, x \notin T, T \subseteq DOMAIN o
    PROVE  P!Write(Image(o, T, t), x, P!Project(o[x], t))
              = Image(o, T \cup {x}, t)
PROOF
    <1> DEFINE proj == P!Project(o[x], t)
    <1>1. T \cup {x} # {}
        BY Z3
    <1>2. Image(o, T \cup {x}, t) = BulkP(o, T \cup {x}, t)
        BY <1>1 DEF Image
    <1>3. CASE T = {}
        <2> DEFINE e(i) == IF i = x THEN proj ELSE o[i]
        <2> DEFINE g(i) == IF i \in {x} THEN P!Project(o[i], t) ELSE o[i]
        <2>1. Image(o, T, t) = o
            BY <1>3 DEF Image
        <2>2. P!Write(o, x, proj)
                = [i \in (DOMAIN o) \cup {x} |-> e(i)]
            BY DEF e, proj, P!Write
        <2>3. (DOMAIN o) \cup {x} = DOMAIN o
            <3>1. \A y : y \in (DOMAIN o) \cup {x} <=> y \in DOMAIN o
                BY Z3
            <3>2. QED
                BY <3>1, IsaWithSetExtensionality
        <2>4. BulkP(o, {x}, t) = [i \in DOMAIN o |-> g(i)]
            BY DEF BulkP, g
        <2>5. \A i \in DOMAIN o : e(i) = g(i)
            BY DEF e, g, proj
        <2>6. P!Write(o, x, proj) = BulkP(o, {x}, t)
            BY <2>2, <2>3, <2>4, <2>5, ExtCtor
        <2>7. T \cup {x} = {x}
            BY <1>3
        <2>8. QED
            BY <1>2, <1>3, <2>1, <2>6, <2>7 DEF proj
    <1>4. CASE T # {}
        <2> DEFINE cur == BulkP(o, T, t)
        <2> DEFINE e(i) == IF i = x THEN proj ELSE cur[i]
        <2> DEFINE g(i) ==
                IF i \in T \cup {x} THEN P!Project(o[i], t) ELSE o[i]
        <2>1. Image(o, T, t) = cur
            BY <1>4 DEF Image, cur
        <2>2. DOMAIN cur = DOMAIN o
            BY DomCtor DEF cur, BulkP
        <2>3. \A i \in DOMAIN o :
                cur[i] = IF i \in T THEN P!Project(o[i], t) ELSE o[i]
            BY <2>2, Z3 DEF cur, BulkP
        <2>4. P!Write(cur, x, proj)
                = [i \in (DOMAIN cur) \cup {x} |-> e(i)]
            BY DEF e, proj, P!Write
        <2>5. (DOMAIN cur) \cup {x} = DOMAIN o
            BY <2>2, Z3
        <2>6. BulkP(o, T \cup {x}, t) = [i \in DOMAIN o |-> g(i)]
            BY DEF BulkP, g
        <2>7. \A i \in DOMAIN o : e(i) = g(i)
            BY <2>3, Z3 DEF e, g, proj
        <2>8. P!Write(cur, x, proj) = BulkP(o, T \cup {x}, t)
            BY <2>4, <2>5, <2>6, <2>7, ExtCtor
        <2>9. QED
            BY <1>2, <2>1, <2>8 DEF proj
    <1>5. QED
        BY <1>3, <1>4

LEMMA TimeoutReach ==
    ASSUME NEW base, NEW box, NEW t, DOMAIN base \subseteq Id
    PROVE  ReachN(base, box, t,
                  Image(base, DueP(base, t), t), box,
                  Cardinality(DueP(base, t)))
PROOF
    <1> DEFINE Due == DueP(base, t)
    <1> DEFINE Closed(T) ==
            \/ T \notin SUBSET Due
            \/ ReachN(base, box, t, Image(base, T, t), box, Cardinality(T))
    <1>1. IsFiniteSet(Due)
        BY DueBound DEF Due
    <1>2. Closed({})
        <2>1. Image(base, {}, t) = base
            BY DEF Image
        <2>2. Cardinality({}) = 0
            BY FS_EmptySet
        <2>3. ReachN(base, box, t, base, box, 0)
            BY ReachZero
        <2>4. QED
            BY <2>1, <2>2, <2>3, Z3 DEF Closed
    <1>3. ASSUME NEW T, NEW x, IsFiniteSet(T), Closed(T), x \notin T
          PROVE  Closed(T \cup {x})
        <2>1. CASE T \cup {x} \notin SUBSET Due
            BY <2>1 DEF Closed
        <2>2. CASE T \cup {x} \in SUBSET Due
            <3>1. /\ T \subseteq Due
                  /\ x \in Due
                  /\ x \notin T
                  /\ T \subseteq DOMAIN base
                  /\ x \in DOMAIN base
                BY <1>3, <2>2, DueSubset, Z3 DEF Due, DueP
            <3>2. ReachN(base, box, t, Image(base, T, t), box, Cardinality(T))
                BY <1>3, <3>1, Z3 DEF Closed
            <3>3. Cardinality(T) \in Nat /\ Cardinality(T \cup {x}) = Cardinality(T) + 1
                BY <1>3, FS_CardinalityType, FS_AddElement, Z3
            <3> DEFINE cur == Image(base, T, t)
            <3>4. /\ x \in DOMAIN cur
                  /\ cur[x] = base[x]
                BY <3>1, ImageAt, Z3 DEF cur
            <3>5. /\ base[x].promise.state = "pending"
                  /\ base[x].promise.timeoutAt <= t
                BY <3>1, Zenon DEF Due, DueP
            <3>5b. /\ cur[x].promise.state = "pending"
                   /\ cur[x].promise.timeoutAt <= t
                BY <3>4, <3>5, Z3
            <3> DEFINE nxt ==
                    Store(P!Write(cur, x, P!Project(cur[x], t)), box)
            <3>6. nxt \in D1(cur, box, t)
                BY <3>4, <3>5b, DuePromiseMember, InDue1, Z3 DEF nxt
            <3>7. P!Write(cur, x, P!Project(cur[x], t))
                    = Image(base, T \cup {x}, t)
                BY <3>1, <3>4, WriteBulk, Z3 DEF cur
            <3>8. ReachN(base, box, t, Image(base, T \cup {x}, t), box,
                         Cardinality(T) + 1)
                BY <3>2, <3>3, <3>6, <3>7, ReachAppend, Z3 DEF nxt
            <3>9. QED
                BY <2>2, <3>3, <3>8 DEF Closed
        <2>3. QED
            BY <2>1, <2>2
    <1>4. Closed(Due)
        <2>1. HIDE DEF Closed
        <2>2. QED
            BY ONLY <1>1, <1>2, <1>3, FS_Induction, Isa
    <1>5. QED
        BY <1>4 DEF Closed, Due

===============================================================================
