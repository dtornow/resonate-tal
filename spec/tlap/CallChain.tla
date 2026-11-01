------------------------------ MODULE CallChain ----------------------------
(* A finite set of callbacks is a chain of due steps. The image of one step
   is CallStep, so the induction only counts. *)
EXTENDS CallJoin

LEMMA CallReach ==
    ASSUME NEW base, NEW box, NEW t, NEW S,
           IsFiniteSet(S),
           S \subseteq DueC(base, t),
           DOMAIN base \subseteq Id,
           \A i \in DOMAIN base : P!Project(base[i], t) = base[i]
    PROVE  ReachN(base, box, t, ImgC(base, S, t), box, Cardinality(S))
PROOF
    <1> DEFINE Due == S
    <1> DEFINE Closed(T) ==
            \/ T \notin SUBSET Due
            \/ ReachN(base, box, t, ImgC(base, T, t), box, Cardinality(T))
    <1>1. IsFiniteSet(Due)
        BY DEF Due
    <1>2. Closed({})
        <2>1. ImgC(base, {}, t) = base
            BY DEF ImgC
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
                  /\ x \in [id : DOMAIN base, awaiter : Id]
                BY <1>3, <2>2, Z3 DEF Due, DueC, IdsC
            <3>2. ReachN(base, box, t, ImgC(base, T, t), box, Cardinality(T))
                BY <1>3, <3>1, Z3 DEF Closed
            <3>3. Cardinality(T) \in Nat
                    /\ Cardinality(T \cup {x}) = Cardinality(T) + 1
                BY <1>3, FS_CardinalityType, FS_AddElement, Z3
            <3> DEFINE cur == ImgC(base, T, t)
            <3> DEFINE i == x.id
            <3> DEFINE w == x.awaiter
            <3>4. i \in DOMAIN base /\ w \in Id /\ i \in IdsC(base, t)
                    /\ w \in base[i].promise.callbacks
                BY <3>1, RecAw, Zenon DEF Due, DueC, IdsC
            <3>5. /\ i \in DOMAIN cur
                  /\ cur[i] = BodyC(base, T, i, t)
                BY <3>4, CallAt DEF cur
            <3>6. P!Project(base[i], t) = base[i]
                BY <3>4
            <3>7. base[i].promise.state /= "pending"
                BY <3>4, <3>6, GuardHeld, Zenon DEF IdsC
            <3>8. /\ cur[i].promise.state = base[i].promise.state
                  /\ cur[i].promise.timeoutAt = base[i].promise.timeoutAt
                  /\ cur[i].promise.callbacks
                        = base[i].promise.callbacks \ Drp(i, T)
                BY <3>4, <3>5, BodyPromise
            <3>8b. w \notin Drp(i, T)
                <4>1. x = [id |-> i, awaiter |-> w]
                    BY <3>1, RecAw DEF i, w
                <4>2. ASSUME w \in Drp(i, T)
                      PROVE  FALSE
                    <5>1. \E p \in T : p.id = i /\ p.awaiter = w
                        BY <4>2 DEF Drp
                    <5>2. PICK p \in T : p.id = i /\ p.awaiter = w
                        BY <5>1
                    <5>3. p \in [id : DOMAIN base, awaiter : Id]
                        BY <3>1, <5>2 DEF Due, DueC, IdsC
                    <5>4. p = [id |-> p.id, awaiter |-> p.awaiter]
                        BY <5>3, RecAw
                    <5>5. p = x
                        BY <4>1, <5>2, <5>4
                    <5>6. QED
                        BY <3>1, <5>2, <5>5
                <4>3. QED
                    BY <4>2
            <3>8c. P!Project(cur[i], t) = cur[i]
                    /\ w \in cur[i].promise.callbacks
                <4>1. \/ base[i].promise.state /= "pending"
                      \/ ~(base[i].promise.timeoutAt <= t)
                    BY <3>6, GuardHeld
                <4>2. \/ cur[i].promise.state /= "pending"
                      \/ ~(cur[i].promise.timeoutAt <= t)
                    BY <3>8, <4>1
                <4>3. P!Project(cur[i], t) = cur[i]
                    BY <4>2, ProjectId
                <4>4. w \in cur[i].promise.callbacks
                    BY <3>4, <3>8, <3>8b, Z3
                <4>5. QED
                    BY <4>3, <4>4
            <3>9. Store(P!CallbackObjects(cur, i, w, t), box)
                    \in P!DueCallback(cur, box, t)
                BY <3>5, <3>7, <3>8, <3>8c, CallMember, Z3
            <3>10. Store(P!CallbackObjects(cur, i, w, t), box) \in D1(cur, box, t)
                BY <3>9, InDue1C
            <3>11. P!CallbackObjects(cur, i, w, t) = ImgC(base, T \cup {x}, t)
                BY <3>1, <3>8b, CallStep DEF i, w, cur
            <3>12. ReachN(base, box, t, ImgC(base, T \cup {x}, t), box,
                          Cardinality(T) + 1)
                BY <3>2, <3>3, <3>10, <3>11, ReachAppend, Z3
            <3>17. QED
                BY <2>2, <3>3, <3>12 DEF Closed
        <2>3. QED
            BY <2>1, <2>2
    <1>4. Closed(Due)
        <2>1. HIDE DEF Closed
        <2>2. QED
            BY ONLY <1>1, <1>2, <1>3, FS_Induction, Isa
    <1>5. QED
        BY <1>4 DEF Closed, Due

===============================================================================
