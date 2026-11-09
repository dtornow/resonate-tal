------------------------------ MODULE CallOn -----------------------------
(* A callback chain whose projection is the identity only at the source and
   the awaiter. One origin, after its timeouts, has that. Other origins may
   still be due. *)
EXTENDS Pass

LEMMA CallStepOn ==
    ASSUME NEW base, NEW T, NEW x, NEW t,
           x \in [id : DOMAIN base, awaiter : Id],
           P!Project(base[x.id], t) = base[x.id],
           x.awaiter \in DOMAIN base => P!Project(base[x.awaiter], t) = base[x.awaiter],
           x.awaiter \notin Drp(x.id, T)
    PROVE  P!CallbackObjects(ImgC(base, T, t), x.id, x.awaiter, t)
              = ImgC(base, T \cup {x}, t)
PROOF
    <1> DEFINE i == x.id
    <1> DEFINE w == x.awaiter
    <1> DEFINE cur == ImgC(base, T, t)
    <1> DEFINE nxt == ImgC(base, T \cup {x}, t)
    <1> DEFINE clear == P!WithoutCallbacks(cur[i], {w})
    <1> DEFINE struck == P!Write(cur, i, clear)
    <1> DEFINE built == [id |-> i, awaiter |-> w]
    <1>1. i \in DOMAIN base /\ w \in Id
        BY Z3 DEF i, w
    <1>2. x = built
        BY <1>1, RecAw, Zenon DEF i, w, built
    <1>3. DOMAIN cur = DOMAIN base
        BY DomImg DEF cur
    <1>4. i \in DOMAIN cur /\ cur[i] = BodyC(base, T, i, t)
        BY <1>1, CallAt DEF cur
    <1>5. P!Project(base[i], t) = base[i]
        BY DEF i
    <1>6. P!Project(cur[i], t) = cur[i]
        BY <1>1, <1>4, <1>5, ProjBody
    <1>7. w \notin Drp(i, T)
        BY DEF i, w
    <1>8. (DOMAIN cur) \cup {i} = DOMAIN base
        BY <1>1, <1>3, Z3
    <1>9. struck = [k \in DOMAIN base |-> IF k = i THEN clear ELSE cur[k]]
        BY <1>8, WriteAs DEF struck
    <1>10. T \cup {x} # {}
        BY Zenon
    <1>11. nxt = [k \in DOMAIN base |-> BodyC(base, T \cup {x}, k, t)]
        BY <1>10 DEF nxt, ImgC
    <1>12. clear = P!WithoutCallbacks(P!Project(cur[i], t), {w})
        BY <1>6 DEF clear
    <1>13. P!CallbackObjects(cur, i, w, t)
            = IF w \notin DOMAIN cur THEN struck
              ELSE LET awaiter == P!Project(struck[w], t)
                   IN  IF awaiter.task.state \in {"none", "fulfilled"}
                          THEN P!Write(struck, w, awaiter)
                       ELSE IF awaiter.task.state = "suspended"
                          THEN P!Write(struck, w, P!WakeSuspended(awaiter, {i}, t))
                       ELSE P!Write(struck, w, P!UnionResumes(awaiter, {i}))
        BY <1>12, Zenon DEF clear, struck, P!CallbackObjects
    <1>14. CASE w \notin DOMAIN base
        <2>1. w \notin DOMAIN cur /\ i # w
            BY <1>1, <1>3, <1>14, Z3
        <2>2. P!CallbackObjects(cur, i, w, t) = struck
            BY <1>13, <2>1
        <2>3. \A k \in DOMAIN base :
                (IF k = i THEN clear ELSE cur[k])
                  = BodyC(base, T \cup {x}, k, t)
            <3> SUFFICES ASSUME NEW k \in DOMAIN base
                         PROVE  (IF k = i THEN clear ELSE cur[k])
                                   = BodyC(base, T \cup {x}, k, t)
                OBVIOUS
            <3>1. CASE k # i
                <4>1. k # w
                    BY <1>14, <3>1, Z3
                <4>2. cur[k] = BodyC(base, T, k, t)
                    BY CallAt
                <4>3. BodyC(base, T \cup {built}, k, t) = BodyC(base, T, k, t)
                    BY <3>1, <4>1, StillBody DEF built
                <4>4. BodyC(base, T \cup {x}, k, t) = BodyC(base, T \cup {built}, k, t)
                    BY <1>2, Zenon
                <4>5. QED
                    BY <3>1, <4>2, <4>3, <4>4 DEF clear
            <3>2. CASE k = i
                <4>1. clear = P!WithoutCallbacks(BodyC(base, T, i, t), {w})
                    BY <1>4 DEF clear
                <4>2. P!WithoutCallbacks(BodyC(base, T, i, t), {w})
                        = BodyC(base, T \cup {built}, i, t)
                    BY <1>1, <1>7, <2>1, ClearOnly
                <4>3. BodyC(base, T \cup {x}, i, t) = BodyC(base, T \cup {built}, i, t)
                    BY <1>2, Zenon
                <4>4. QED
                    BY <3>2, <4>1, <4>2, <4>3
            <3>3. QED
                BY <3>1, <3>2
        <2>4. [k \in DOMAIN base |-> IF k = i THEN clear ELSE cur[k]]
                = [k \in DOMAIN base |-> BodyC(base, T \cup {x}, k, t)]
            BY <2>3, ExtCtor
        <2>5. QED
            BY <1>9, <1>11, <2>2, <2>4
    <1>15. CASE w \in DOMAIN base
        <2> DEFINE awaiter == P!Project(struck[w], t)
        <2> DEFINE wake ==
                IF awaiter.task.state \in {"none", "fulfilled"} THEN awaiter
                ELSE IF awaiter.task.state = "suspended"
                     THEN P!WakeSuspended(awaiter, {i}, t)
                ELSE P!UnionResumes(awaiter, {i})
        <2>1. w \in DOMAIN cur
            BY <1>3, <1>15
        <2>2. P!CallbackObjects(cur, i, w, t) = P!Write(struck, w, wake)
            BY <1>13, <2>1 DEF awaiter, wake
        <2>3. ASSUME w # i
              PROVE  wake = BodyC(base, T \cup {built}, w, t)
            <3>1a. w # i /\ w \in DOMAIN base
                BY <1>15, <2>3
            <3>1b. w \in (DOMAIN cur) \cup {i}
                BY <1>3, <3>1a, Z3
            <3>1c. struck[w] = IF w = i THEN clear ELSE cur[w]
                BY <3>1b, WriteAt DEF struck
            <3>1. struck[w] = cur[w]
                BY <3>1a, <3>1c, Zenon
            <3>2. cur[w] = BodyC(base, T, w, t)
                BY <1>15, CallAt DEF cur
            <3>3. P!Project(base[w], t) = base[w]
                BY <1>15 DEF w
            <3>4. P!Project(BodyC(base, T, w, t), t) = BodyC(base, T, w, t)
                BY <1>15, <3>3, ProjBody
            <3>5. awaiter = cur[w]
                BY <3>1, <3>2, <3>4 DEF awaiter
            <3>6. wake = WakeOne(cur[w], {i}, t)
                BY <3>5 DEF wake, WakeOne
            <3>7. WakeOne(BodyC(base, T, w, t), {i}, t)
                    = BodyC(base, T \cup {built}, w, t)
                BY <1>15, <2>3, <3>1a, WakeOnly DEF built
            <3>8. QED
                BY <3>2, <3>6, <3>7
        <2>4. ASSUME w = i
              PROVE  wake = BodyC(base, T \cup {built}, i, t)
            <3>1a. w = i /\ w \in DOMAIN base
                BY <1>15, <2>4
            <3>1b. w \in (DOMAIN cur) \cup {i}
                BY <1>3, <3>1a, Z3
            <3>1c. struck[w] = IF w = i THEN clear ELSE cur[w]
                BY <3>1b, WriteAt DEF struck
            <3>1. struck[w] = clear
                BY <3>1a, <3>1c, Zenon
            <3>2. P!Project(clear, t) = clear
                BY <1>6, ProjectClear DEF clear
            <3>3. awaiter = clear
                BY <3>1, <3>2 DEF awaiter
            <3>4. wake = WakeOne(clear, {i}, t)
                BY <3>3 DEF wake, WakeOne
            <3>5. clear = P!WithoutCallbacks(BodyC(base, T, i, t), {i})
                BY <1>4, <3>1a, Zenon DEF clear
            <3>6. i \notin Drp(i, T)
                BY <1>7, <3>1a, Zenon
            <3>6b. WakeOne(P!WithoutCallbacks(BodyC(base, T, i, t), {i}), {i}, t)
                    = BodyC(base, T \cup {built}, i, t)
                BY <1>1, <3>1a, <3>6, SelfOnly DEF built
            <3>7. QED
                BY <3>4, <3>5, <3>6b
        <2>5. \A k \in DOMAIN base :
                (IF k = w THEN wake ELSE struck[k])
                  = BodyC(base, T \cup {x}, k, t)
            <3> SUFFICES ASSUME NEW k \in DOMAIN base
                         PROVE  (IF k = w THEN wake ELSE struck[k])
                                   = BodyC(base, T \cup {x}, k, t)
                OBVIOUS
            <3>1. struck[k] = IF k = i THEN clear ELSE cur[k]
                BY <1>9, Z3
            <3>2. CASE k # i /\ k # w
                <4>1. cur[k] = BodyC(base, T, k, t)
                    BY CallAt
                <4>2. BodyC(base, T \cup {built}, k, t) = BodyC(base, T, k, t)
                    BY <3>2, StillBody DEF built
                <4>3. BodyC(base, T \cup {x}, k, t) = BodyC(base, T \cup {built}, k, t)
                    BY <1>2, Zenon
                <4>4. QED
                    BY <3>1, <3>2, <4>1, <4>2, <4>3
            <3>3. CASE k = i /\ k # w
                <4>1. P!WithoutCallbacks(BodyC(base, T, i, t), {w})
                        = BodyC(base, T \cup {built}, i, t)
                    BY <1>1, <1>7, <3>3, ClearOnly
                <4>2. clear = P!WithoutCallbacks(BodyC(base, T, i, t), {w})
                    BY <1>4 DEF clear
                <4>3. BodyC(base, T \cup {x}, i, t) = BodyC(base, T \cup {built}, i, t)
                    BY <1>2, Zenon
                <4>4. QED
                    BY <3>1, <3>3, <4>1, <4>2, <4>3
            <3>4. CASE k = w /\ k # i
                <4>1. w # i
                    BY <3>4
                <4>2. wake = BodyC(base, T \cup {built}, w, t)
                    BY <2>3, <4>1
                <4>3. BodyC(base, T \cup {x}, w, t) = BodyC(base, T \cup {built}, w, t)
                    BY <1>2, Zenon
                <4>4. QED
                    BY <3>4, <4>2, <4>3
            <3>5. CASE k = w /\ k = i
                <4>1. w = i
                    BY <3>5
                <4>2. wake = BodyC(base, T \cup {built}, i, t)
                    BY <2>4, <4>1
                <4>3. BodyC(base, T \cup {x}, i, t) = BodyC(base, T \cup {built}, i, t)
                    BY <1>2, Zenon
                <4>4. QED
                    BY <3>5, <4>2, <4>3
            <3>6. QED
                BY <3>2, <3>3, <3>4, <3>5
        <2>6. DOMAIN struck = DOMAIN base
            BY <1>9, DomCtor
        <2>7. (DOMAIN struck) \cup {w} = DOMAIN base
            BY <1>15, <2>6, Z3
        <2>8. P!Write(struck, w, wake)
                = [k \in DOMAIN base |-> IF k = w THEN wake ELSE struck[k]]
            BY <2>7, WriteAs
        <2>9. P!Write(struck, w, wake) = nxt
            BY <1>11, <2>5, <2>8, ExtCtor
        <2>10. QED
            BY <2>2, <2>9 DEF nxt
    <1>16. QED
        BY <1>14, <1>15


LEMMA CallOn ==
    ASSUME NEW base, NEW box, NEW t, NEW S,
           IsFiniteSet(S),
           S \subseteq DueC(base, t),
           DOMAIN base \subseteq Id,
           \A y \in S : P!Project(base[y.id], t) = base[y.id],
           \A y \in S : y.awaiter \in DOMAIN base =>
                              P!Project(base[y.awaiter], t) = base[y.awaiter]
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
                BY <3>1 DEF Due, i
            <3>6b. w \in DOMAIN base => P!Project(base[w], t) = base[w]
                BY <3>1 DEF Due, w
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
                BY <3>1, <3>6, <3>6b, <3>8b, CallStepOn DEF i, w, cur
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
