------------------------------- MODULE Retry -------------------------------
(* A retry pass writes one id and posts one Execute. Keys are the id, so the
   outbox does not depend on the order of the ids. *)
EXTENDS Proj

RetryBody(obj, t) ==
    [obj EXCEPT !.task.retryTimeoutAt = t + RetryTimeout]

RetryMsg(o, i) ==
    [ address |-> o[i].promise.tags.target,
      message |-> [ tag     |-> "Execute",
                    id      |-> i,
                    version |-> o[i].task.version ] ]

DueR(o, t) ==
    { j \in DOMAIN o :
        /\ o[j].task.state = "pending"
        /\ o[j].task.retryTimeoutAt /= NoTime
        /\ o[j].task.retryTimeoutAt <= t
        /\ P!Project(o[j], t).promise.state = "pending" }

Msgs(o, T) ==
    { RetryMsg(o, i) : i \in T }

ImgR(o, T, t) ==
    IF T = {} THEN o
    ELSE [ i \in DOMAIN o |-> IF i \in T THEN RetryBody(o[i], t) ELSE o[i] ]

BoxAt(b, o, T) ==
    Posted(b, Msgs(o, T))

LEMMA RetryMember ==
    ASSUME NEW o, NEW b, NEW t, NEW i \in DOMAIN o,
           i \in DueR(o, t)
    PROVE  Store(P!Write(o, i, RetryBody(o[i], t)), Post(b, RetryMsg(o, i)))
              \in P!DueRetry(o, b, t)
PROOF
    <1> DEFINE old == o[i]
    <1> DEFINE msg ==
            [ address |-> old.promise.tags.target,
              message |-> [ tag     |-> "Execute",
                            id      |-> i,
                            version |-> old.task.version ] ]
    <1> DEFINE guard(j) ==
            LET prev == o[j]
            IN  /\ prev.task.state = "pending"
                /\ prev.task.retryTimeoutAt /= P!NoTime
                /\ prev.task.retryTimeoutAt <= t
                /\ P!Project(prev, t).promise.state = "pending"
    <1>1. NoTime = P!NoTime
        BY DEF NoTime, P!NoTime
    <1>2. i \in { j \in DOMAIN o : guard(j) }
        BY <1>1, Zenon DEF DueR, guard
    <1>3. RetryBody(o[i], t) = [old EXCEPT !.task.retryTimeoutAt = t + RetryTimeout]
        BY DEF RetryBody, old
    <1>4. RetryMsg(o, i) = msg
        BY DEF RetryMsg, msg, old
    <1>5. \A e : MsgKey(e) = P!MsgKey(e)
        BY Zenon DEF MsgKey, P!MsgKey
    <1>6. Post(b, msg) = { x \in b : P!MsgKey(x) /= P!MsgKey(msg) } \cup {msg}
        <2>1. \A y : y \in Post(b, msg)
                       <=> y \in { x \in b : P!MsgKey(x) /= P!MsgKey(msg) } \cup {msg}
            BY <1>5, Zenon DEF Post
        <2>2. QED
            BY <2>1, SetExtensionality
    <1>7. Store(P!Write(o, i, [old EXCEPT !.task.retryTimeoutAt = t + RetryTimeout]),
                { x \in b : P!MsgKey(x) /= P!MsgKey(msg) } \cup {msg})
            \in P!DueRetry(o, b, t)
        BY <1>2, Zenon DEF Store, P!DueRetry, old, msg, guard
    <1>8. QED
        BY <1>3, <1>4, <1>6, <1>7

LEMMA InDue1R ==
    ASSUME NEW o, NEW b, NEW t, NEW st \in P!DueRetry(o, b, t)
    PROVE  st \in D1(o, b, t)
PROOF
    BY DEF D1, P!Due1

LEMMA ExecKey ==
    ASSUME NEW o, NEW i \in DOMAIN o, NEW j \in DOMAIN o, i /= j
    PROVE  MsgKey(RetryMsg(o, i)) /= MsgKey(RetryMsg(o, j))
PROOF
    BY DEF MsgKey, RetryMsg

LEMMA RetrySubset ==
    ASSUME NEW o, NEW t
    PROVE  DueR(o, t) \subseteq DOMAIN o
PROOF
    BY DEF DueR

LEMMA RetryBound ==
    ASSUME NEW base, NEW t, DOMAIN base \subseteq Id
    PROVE  /\ IsFiniteSet(DueR(base, t))
           /\ Cardinality(DueR(base, t)) \in 0 .. P!MaxSweep
PROOF
    <1>1. DueR(base, t) \subseteq Id
        BY RetrySubset, Z3
    <1>2. IsFiniteSet(Id) /\ Cardinality(Id) <= P!MaxSweep /\ P!MaxSweep \in Nat
        BY FiniteOrigin, FiniteRest, IdFinite, SweepCap
    <1>3. /\ IsFiniteSet(DueR(base, t))
          /\ Cardinality(DueR(base, t)) <= Cardinality(Id)
        BY <1>1, <1>2, FS_Subset
    <1>4. Cardinality(Id) \in Nat /\ Cardinality(DueR(base, t)) \in Nat
        BY <1>2, <1>3, FS_CardinalityType
    <1>5. QED
        BY <1>2, <1>3, <1>4, Z3

LEMMA MsgUnion ==
    ASSUME NEW o, NEW T, NEW x,
           x \in DOMAIN o, x \notin T, T \subseteq DOMAIN o
    PROVE  Msgs(o, T \cup {x}) = Msgs(o, T) \cup {RetryMsg(o, x)}
PROOF
    <1>1. \A y : y \in Msgs(o, T \cup {x}) <=> y \in Msgs(o, T) \cup {RetryMsg(o, x)}
        BY Zenon DEF Msgs
    <1>2. QED
        BY <1>1, IsaWithSetExtensionality

LEMMA FreshKey ==
    ASSUME NEW o, NEW T, NEW x,
           x \in DOMAIN o, x \notin T, T \subseteq DOMAIN o
    PROVE  \A m \in Msgs(o, T) : MsgKey(m) /= MsgKey(RetryMsg(o, x))
PROOF
    <1> SUFFICES ASSUME NEW m \in Msgs(o, T)
                 PROVE  MsgKey(m) /= MsgKey(RetryMsg(o, x))
        OBVIOUS
    <1>1. \E i \in T : m = RetryMsg(o, i)
        BY DEF Msgs
    <1>2. PICK i \in T : m = RetryMsg(o, i)
        BY <1>1
    <1>3. i /= x /\ i \in DOMAIN o
        BY <1>2
    <1>4. QED
        BY <1>2, <1>3, ExecKey

LEMMA BoxStepR ==
    ASSUME NEW b, NEW o, NEW T, NEW x,
           x \in DOMAIN o, x \notin T, T \subseteq DOMAIN o
    PROVE  Post(BoxAt(b, o, T), RetryMsg(o, x)) = BoxAt(b, o, T \cup {x})
PROOF
    <1>1. \A m \in Msgs(o, T) : MsgKey(m) /= MsgKey(RetryMsg(o, x))
        BY FreshKey
    <1>2. Post(Posted(b, Msgs(o, T)), RetryMsg(o, x))
            = Posted(b, Msgs(o, T) \cup {RetryMsg(o, x)})
        BY <1>1, PostedStep
    <1>3. Msgs(o, T) \cup {RetryMsg(o, x)} = Msgs(o, T \cup {x})
        BY MsgUnion
    <1>4. QED
        BY <1>2, <1>3 DEF BoxAt

LEMMA RetryAt ==
    ASSUME NEW o, NEW T, NEW t, NEW x,
           x \in DOMAIN o, x \notin T, T \subseteq DOMAIN o
    PROVE  /\ x \in DOMAIN ImgR(o, T, t)
           /\ ImgR(o, T, t)[x] = o[x]
PROOF
    <1>1. CASE T = {}
        BY <1>1 DEF ImgR
    <1>2. CASE T # {}
        <2> DEFINE body ==
                [ i \in DOMAIN o |-> IF i \in T THEN RetryBody(o[i], t) ELSE o[i] ]
        <2>1. ImgR(o, T, t) = body
            BY <1>2 DEF ImgR, body
        <2>2. DOMAIN body = DOMAIN o
            BY DomCtor DEF body
        <2>3. QED
            BY <1>2, <2>1, <2>2, Z3 DEF body
    <1>3. QED
        BY <1>1, <1>2

LEMMA RetryBulk ==
    ASSUME NEW o, NEW T, NEW t, NEW x,
           x \in DOMAIN o, x \notin T, T \subseteq DOMAIN o
    PROVE  P!Write(ImgR(o, T, t), x, RetryBody(o[x], t))
              = ImgR(o, T \cup {x}, t)
PROOF
    <1> DEFINE proj == RetryBody(o[x], t)
    <1>1. T \cup {x} # {}
        BY Z3
    <1>2. ImgR(o, T \cup {x}, t)
            = [ i \in DOMAIN o |-> IF i \in T \cup {x} THEN RetryBody(o[i], t) ELSE o[i] ]
        BY <1>1 DEF ImgR
    <1>3. CASE T = {}
        <2> DEFINE e(i) == IF i = x THEN proj ELSE o[i]
        <2> DEFINE g(i) == IF i \in {x} THEN RetryBody(o[i], t) ELSE o[i]
        <2>1. ImgR(o, T, t) = o
            BY <1>3 DEF ImgR
        <2>2. P!Write(o, x, proj) = [i \in (DOMAIN o) \cup {x} |-> e(i)]
            BY DEF e, proj, P!Write
        <2>3. (DOMAIN o) \cup {x} = DOMAIN o
            <3>1. \A y : y \in (DOMAIN o) \cup {x} <=> y \in DOMAIN o
                BY Z3
            <3>2. QED
                BY <3>1, IsaWithSetExtensionality
        <2>4. [ i \in DOMAIN o |-> IF i \in {x} THEN RetryBody(o[i], t) ELSE o[i] ]
                = [ i \in DOMAIN o |-> g(i) ]
            BY DEF g
        <2>5. \A i \in DOMAIN o : e(i) = g(i)
            BY Z3 DEF e, g, proj
        <2>6. P!Write(o, x, proj)
                = [ i \in DOMAIN o |-> IF i \in {x} THEN RetryBody(o[i], t) ELSE o[i] ]
            BY <2>2, <2>3, <2>4, <2>5, ExtCtor
        <2>7. T \cup {x} = {x}
            BY <1>3
        <2>8. QED
            BY <1>2, <1>3, <2>1, <2>6, <2>7
    <1>4. CASE T # {}
        <2> DEFINE cur ==
                [ i \in DOMAIN o |-> IF i \in T THEN RetryBody(o[i], t) ELSE o[i] ]
        <2> DEFINE e(i) == IF i = x THEN proj ELSE cur[i]
        <2> DEFINE g(i) == IF i \in T \cup {x} THEN RetryBody(o[i], t) ELSE o[i]
        <2>1. ImgR(o, T, t) = cur
            BY <1>4 DEF ImgR, cur
        <2>2. DOMAIN cur = DOMAIN o
            BY DomCtor DEF cur
        <2>3. \A i \in DOMAIN o : cur[i] = IF i \in T THEN RetryBody(o[i], t) ELSE o[i]
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

LEMMA RetryReach ==
    ASSUME NEW base, NEW box, NEW t, DOMAIN base \subseteq Id
    PROVE  ReachN(base, box, t,
                  ImgR(base, DueR(base, t), t),
                  BoxAt(box, base, DueR(base, t)),
                  Cardinality(DueR(base, t)))
PROOF
    <1> DEFINE Due == DueR(base, t)
    <1> DEFINE Closed(T) ==
            \/ T \notin SUBSET Due
            \/ ReachN(base, box, t, ImgR(base, T, t), BoxAt(box, base, T),
                      Cardinality(T))
    <1>1. IsFiniteSet(Due)
        BY RetryBound DEF Due
    <1>2. Closed({})
        <2>1. ImgR(base, {}, t) = base
            BY DEF ImgR
        <2>2. BoxAt(box, base, {}) = box
            <3>1. Msgs(base, {}) = {}
                BY DEF Msgs
            <3>2. QED
                BY <3>1 DEF BoxAt, Posted
        <2>3. Cardinality({}) = 0
            BY FS_EmptySet
        <2>4. ReachN(base, box, t, base, box, 0)
            BY ReachZero
        <2>5. QED
            BY <2>1, <2>2, <2>3, <2>4, Z3 DEF Closed
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
                BY <1>3, <2>2, RetrySubset, Z3 DEF Due
            <3>2. ReachN(base, box, t, ImgR(base, T, t), BoxAt(box, base, T),
                         Cardinality(T))
                BY <1>3, <3>1, Z3 DEF Closed
            <3>3. Cardinality(T) \in Nat
                    /\ Cardinality(T \cup {x}) = Cardinality(T) + 1
                BY <1>3, FS_CardinalityType, FS_AddElement, Z3
            <3> DEFINE cur == ImgR(base, T, t)
            <3> DEFINE curb == BoxAt(box, base, T)
            <3>4. /\ x \in DOMAIN cur
                  /\ cur[x] = base[x]
                BY <3>1, RetryAt, Z3 DEF cur
            <3>5. x \in DueR(cur, t)
                BY <3>1, <3>4, Zenon DEF Due, DueR
            <3>6. RetryBody(cur[x], t) = RetryBody(base[x], t)
                BY <3>4, Z3 DEF RetryBody
            <3>7. RetryMsg(cur, x) = RetryMsg(base, x)
                BY <3>4, Z3 DEF RetryMsg
            <3>8. Store(P!Write(cur, x, RetryBody(base[x], t)),
                        Post(curb, RetryMsg(base, x)))
                    \in P!DueRetry(cur, curb, t)
                BY <3>4, <3>5, <3>6, <3>7, RetryMember, Z3
            <3>9. Store(P!Write(cur, x, RetryBody(base[x], t)),
                        Post(curb, RetryMsg(base, x)))
                    \in D1(cur, curb, t)
                BY <3>8, InDue1R
            <3>10. P!Write(cur, x, RetryBody(base[x], t)) = ImgR(base, T \cup {x}, t)
                BY <3>1, RetryBulk, Z3 DEF cur
            <3>11. Post(curb, RetryMsg(base, x)) = BoxAt(box, base, T \cup {x})
                BY <3>1, BoxStepR DEF curb
            <3>12. ReachN(base, box, t, ImgR(base, T \cup {x}, t),
                          BoxAt(box, base, T \cup {x}), Cardinality(T) + 1)
                BY <3>2, <3>3, <3>9, <3>10, <3>11, ReachAppend, Z3
            <3>13. QED
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
