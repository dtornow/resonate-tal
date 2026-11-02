------------------------------- MODULE Gen --------------------------------
(* Any set of per-id writes, each one a due step, is a chain. Passes that
   touch one id once — timeouts, leases, retries — are instances of this. *)
EXTENDS Reach

Img(o, T, Upd(_)) ==
    IF T = {} THEN o
    ELSE [ i \in DOMAIN o |-> IF i \in T THEN Upd(i) ELSE o[i] ]

LEMMA GenAt ==
    ASSUME NEW o, NEW T, NEW x, NEW Upd(_),
           x \in DOMAIN o, x \notin T, T \subseteq DOMAIN o
    PROVE  /\ x \in DOMAIN Img(o, T, Upd)
           /\ Img(o, T, Upd)[x] = o[x]
PROOF
    <1>1. CASE T = {}
        BY <1>1 DEF Img
    <1>2. CASE T # {}
        <2> DEFINE body == [ i \in DOMAIN o |-> IF i \in T THEN Upd(i) ELSE o[i] ]
        <2>1. Img(o, T, Upd) = body
            BY <1>2 DEF Img, body
        <2>2. DOMAIN body = DOMAIN o
            BY DomCtor DEF body
        <2>3. QED
            BY <1>2, <2>1, <2>2, Z3 DEF body
    <1>3. QED
        BY <1>1, <1>2

LEMMA GenBulk ==
    ASSUME NEW o, NEW T, NEW x, NEW Upd(_),
           x \in DOMAIN o, x \notin T, T \subseteq DOMAIN o
    PROVE  P!Write(Img(o, T, Upd), x, Upd(x)) = Img(o, T \cup {x}, Upd)
PROOF
    <1> DEFINE proj == Upd(x)
    <1>1. T \cup {x} # {}
        BY Z3
    <1>2. Img(o, T \cup {x}, Upd)
            = [ i \in DOMAIN o |-> IF i \in T \cup {x} THEN Upd(i) ELSE o[i] ]
        BY <1>1 DEF Img
    <1>3. CASE T = {}
        <2> DEFINE e(i) == IF i = x THEN proj ELSE o[i]
        <2> DEFINE g(i) == IF i \in {x} THEN Upd(i) ELSE o[i]
        <2>1. Img(o, T, Upd) = o
            BY <1>3 DEF Img
        <2>2. P!Write(o, x, proj) = [i \in (DOMAIN o) \cup {x} |-> e(i)]
            BY DEF e, proj, P!Write
        <2>3. (DOMAIN o) \cup {x} = DOMAIN o
            <3>1. \A y : y \in (DOMAIN o) \cup {x} <=> y \in DOMAIN o
                BY Z3
            <3>2. QED
                BY <3>1, IsaWithSetExtensionality
        <2>4. [ i \in DOMAIN o |-> IF i \in {x} THEN Upd(i) ELSE o[i] ]
                = [ i \in DOMAIN o |-> g(i) ]
            BY DEF g
        <2>5. \A i \in DOMAIN o : e(i) = g(i)
            BY Z3 DEF e, g, proj
        <2>6. P!Write(o, x, proj)
                = [ i \in DOMAIN o |-> IF i \in {x} THEN Upd(i) ELSE o[i] ]
            BY <2>2, <2>3, <2>4, <2>5, ExtCtor
        <2>7. T \cup {x} = {x}
            BY <1>3
        <2>8. QED
            BY <1>2, <1>3, <2>1, <2>6, <2>7
    <1>4. CASE T # {}
        <2> DEFINE cur == [ i \in DOMAIN o |-> IF i \in T THEN Upd(i) ELSE o[i] ]
        <2> DEFINE e(i) == IF i = x THEN proj ELSE cur[i]
        <2> DEFINE g(i) == IF i \in T \cup {x} THEN Upd(i) ELSE o[i]
        <2>1. Img(o, T, Upd) = cur
            BY <1>4 DEF Img, cur
        <2>2. DOMAIN cur = DOMAIN o
            BY DomCtor DEF cur
        <2>3. \A i \in DOMAIN o : cur[i] = IF i \in T THEN Upd(i) ELSE o[i]
            BY Z3 DEF cur
        <2>4. P!Write(cur, x, proj) = [i \in (DOMAIN cur) \cup {x} |-> e(i)]
            BY DEF e, proj, P!Write
        <2>5. (DOMAIN cur) \cup {x} = DOMAIN o
            <3>1. \A y : y \in (DOMAIN cur) \cup {x} <=> y \in DOMAIN o
                BY <2>2, Z3
            <3>2. QED
                BY <3>1, IsaWithSetExtensionality
        <2>6. \A i \in DOMAIN o : e(i) = g(i)
            BY <2>3, Z3 DEF e, g, proj
        <2>7. P!Write(cur, x, proj) = [i \in DOMAIN o |-> g(i)]
            BY <2>4, <2>5, <2>6, ExtCtor
        <2>8. QED
            BY <1>2, <2>1, <2>7 DEF g
    <1>5. QED
        BY <1>3, <1>4

LEMMA GenFold ==
    ASSUME NEW base, NEW box, NEW t, NEW S, NEW Upd(_),
           IsFiniteSet(S), S \subseteq DOMAIN base,
           \A T, x :
              T \subseteq S /\ x \in S /\ x \notin T =>
                 Store(P!Write(Img(base, T, Upd), x, Upd(x)), box)
                   \in D1(Img(base, T, Upd), box, t)
    PROVE  ReachN(base, box, t, Img(base, S, Upd), box, Cardinality(S))
PROOF
    <1> DEFINE Closed(T) ==
            \/ T \notin SUBSET S
            \/ ReachN(base, box, t, Img(base, T, Upd), box, Cardinality(T))
    <1>1. IsFiniteSet(S)
        OBVIOUS
    <1>2. Closed({})
        <2>1. Img(base, {}, Upd) = base
            BY DEF Img
        <2>2. Cardinality({}) = 0
            BY FS_EmptySet
        <2>3. ReachN(base, box, t, base, box, 0)
            BY ReachZero
        <2>4. QED
            BY <2>1, <2>2, <2>3, Z3 DEF Closed
    <1>3. ASSUME NEW T, NEW x, IsFiniteSet(T), Closed(T), x \notin T
          PROVE  Closed(T \cup {x})
        <2>1. CASE T \cup {x} \notin SUBSET S
            BY <2>1 DEF Closed
        <2>2. CASE T \cup {x} \in SUBSET S
            <3>1. T \subseteq S /\ x \in S /\ x \notin T /\ T \subseteq DOMAIN base /\ x \in DOMAIN base
                BY <1>3, <2>2, Z3
            <3>2. ReachN(base, box, t, Img(base, T, Upd), box, Cardinality(T))
                BY <1>3, <3>1, Z3 DEF Closed
            <3>3. Cardinality(T) \in Nat /\ Cardinality(T \cup {x}) = Cardinality(T) + 1
                BY <1>3, FS_CardinalityType, FS_AddElement, Z3
            <3> DEFINE cur == Img(base, T, Upd)
            <3>4. Store(P!Write(cur, x, Upd(x)), box) \in D1(cur, box, t)
                BY <3>1, Zenon DEF cur
            <3>5. P!Write(cur, x, Upd(x)) = Img(base, T \cup {x}, Upd)
                BY <3>1, GenBulk DEF cur
            <3>6. ReachN(base, box, t, Img(base, T \cup {x}, Upd), box, Cardinality(T) + 1)
                BY <3>2, <3>3, <3>4, <3>5, ReachAppend, Z3
            <3>7. QED
                BY <2>2, <3>3, <3>6 DEF Closed
        <2>3. QED
            BY <2>1, <2>2
    <1>4. Closed(S)
        <2>1. HIDE DEF Closed
        <2>2. QED
            BY ONLY <1>1, <1>2, <1>3, FS_Induction, Isa
    <1>5. QED
        BY <1>4 DEF Closed

LEMMA ReachCat ==
    ASSUME NEW base, NEW box, NEW t, NEW mid, NEW bmid, NEW os, NEW b,
           NEW n \in Nat, NEW m \in Nat,
           ReachN(base, box, t, mid, bmid, n),
           ReachN(mid, bmid, t, os, b, m)
    PROVE  ReachN(base, box, t, os, b, n + m)
PROOF
    <1>1. PICK c1 :
            /\ c1[0] = Store(base, box)
            /\ StepOk(c1, t, n)
            /\ c1[n] = Store(mid, bmid)
        BY DEF ReachN
    <1>2. PICK c2 :
            /\ c2[0] = Store(mid, bmid)
            /\ StepOk(c2, t, m)
            /\ c2[m] = Store(os, b)
        BY DEF ReachN
    <1> DEFINE c ==
            [ i \in 0 .. (n + m) |-> IF i <= n THEN c1[i] ELSE c2[i - n] ]
    <1>3. c[0] = Store(base, box) /\ c[n + m] = Store(os, b)
        BY <1>1, <1>2, Z3 DEF c
    <1>4. StepOk(c, t, n + m)
        <2>1. DOMAIN c = 0 .. (n + m)
            BY Z3 DEF c
        <2>2. \A i \in 0 .. ((n + m) - 1) :
                c[i + 1] \in D1(c[i].objects, c[i].outbox, t)
            <3> SUFFICES ASSUME NEW i \in 0 .. ((n + m) - 1)
                         PROVE  c[i + 1] \in D1(c[i].objects, c[i].outbox, t)
                OBVIOUS
            <3>1. CASE i < n
                BY <1>1, <3>1, Z3 DEF c, StepOk
            <3>2. CASE i >= n
                BY <1>1, <1>2, <3>2, Z3 DEF c, StepOk
            <3>3. QED
                BY <3>1, <3>2, Z3
        <2>3. QED
            BY <2>1, <2>2, Zenon DEF StepOk
    <1>5. QED
        BY <1>3, <1>4 DEF ReachN

===============================================================================
