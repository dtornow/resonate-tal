------------------------------- MODULE Proj --------------------------------
(* Projection after a timeout pass, a due-promise chain for any subset of
   the due ids, and replace-by-key on the outbox. *)
EXTENDS Lease

LEMMA SameProject ==
    ASSUME NEW obj, NEW t
    PROVE  Project(obj, t) = P!Project(obj, t)
PROOF
    BY Isa DEF Project, P!Project, NoTime, P!NoTime, NoTask, P!NoTask

LEMMA SameNew ==
    ASSUME NEW req, NEW t
    PROVE  New(req, t) = P!New(req, t)
PROOF
    BY Isa DEF New, P!New, NoTime, P!NoTime, NoTask, P!NoTask

LEMMA SameWrite ==
    ASSUME NEW doc, NEW i, NEW obj
    PROVE  Write(doc, i, obj) = P!Write(doc, i, obj)
PROOF
    BY DEF Write, P!Write

LEMMA ProjectTwice ==
    ASSUME NEW obj, NEW t
    PROVE  P!Project(P!Project(obj, t), t) = P!Project(obj, t)
PROOF
    <1> DEFINE p == P!Project(obj, t)
    <1>1. CASE obj.promise.state = "pending" /\ obj.promise.timeoutAt <= t
        <2> DEFINE st == IF obj.promise.tags.timer THEN "resolved"
                         ELSE "rejectedTimedout"
        <2> DEFINE p1 == [obj.promise EXCEPT !.state = st]
        <2> DEFINE p2 == [p1 EXCEPT !.value = NoValue]
        <2> DEFINE p3 == [p2 EXCEPT !.settledAt = obj.promise.timeoutAt]
        <2>1. p1.state = st
            BY Z3 DEF p1
        <2>2. p2.state = p1.state /\ p3.state = p2.state
            BY Z3 DEF p2, p3
        <2>3. p.promise = p3
            BY <1>1, Zenon DEF p, st, p1, p2, p3, P!Project
        <2>4. p.promise.state = st /\ st /= "pending"
            BY <2>1, <2>2, <2>3
        <2>5. P!Project(p, t) = p
            BY <2>4, ProjectId
        <2>6. QED
            BY <2>5 DEF p
    <1>2. CASE obj.promise.state /= "pending" \/ ~(obj.promise.timeoutAt <= t)
        <2>1. p = obj
            BY <1>2, ProjectId DEF p
        <2>2. QED
            BY <2>1, Zenon DEF p
    <1>3. QED
        BY <1>1, <1>2

LEMMA ImageVal ==
    ASSUME NEW o, NEW T, NEW t, NEW i,
           i \in DOMAIN o, T \subseteq DOMAIN o
    PROVE  /\ i \in DOMAIN Image(o, T, t)
           /\ Image(o, T, t)[i]
                = IF i \in T THEN P!Project(o[i], t) ELSE o[i]
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

LEMMA ProjectFixed ==
    ASSUME NEW base, NEW t, NEW i \in DOMAIN base
    PROVE  P!Project(Image(base, DueP(base, t), t)[i], t)
              = Image(base, DueP(base, t), t)[i]
PROOF
    <1> DEFINE Due == DueP(base, t)
    <1> DEFINE im == Image(base, Due, t)
    <1>1. Due \subseteq DOMAIN base
        BY DueSubset DEF Due
    <1>2. /\ i \in DOMAIN im
          /\ im[i] = IF i \in Due THEN P!Project(base[i], t) ELSE base[i]
        BY <1>1, ImageVal DEF im
    <1>3. CASE i \in Due
        <2>1. im[i] = P!Project(base[i], t)
            BY <1>2, <1>3
        <2>2. QED
            BY <2>1, ProjectTwice
    <1>4. CASE i \notin Due
        <2>1. im[i] = base[i]
            BY <1>2, <1>4
        <2>2. \/ base[i].promise.state /= "pending"
              \/ ~(base[i].promise.timeoutAt <= t)
            BY <1>4, Zenon DEF Due, DueP
        <2>3. P!Project(base[i], t) = base[i]
            BY <2>2, ProjectId
        <2>4. QED
            BY <2>1, <2>3
    <1>5. QED
        BY <1>3, <1>4

LEMMA TimeoutSub ==
    ASSUME NEW base, NEW box, NEW t, NEW S,
           IsFiniteSet(S), S \subseteq DueP(base, t)
    PROVE  ReachN(base, box, t, Image(base, S, t), box, Cardinality(S))
PROOF
    <1> DEFINE Due == S
    <1> DEFINE Closed(T) ==
            \/ T \notin SUBSET Due
            \/ ReachN(base, box, t, Image(base, T, t), box, Cardinality(T))
    <1>1. IsFiniteSet(Due)
        BY DEF Due
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
            <3>3. Cardinality(T) \in Nat
                    /\ Cardinality(T \cup {x}) = Cardinality(T) + 1
                BY <1>3, FS_CardinalityType, FS_AddElement, Z3
            <3> DEFINE cur == Image(base, T, t)
            <3>4. /\ x \in DOMAIN cur
                  /\ cur[x] = base[x]
                BY <3>1, ImageAt, Z3 DEF cur
            <3>4b. x \in DueP(base, t)
                BY <3>1 DEF Due
            <3>5. /\ base[x].promise.state = "pending"
                  /\ base[x].promise.timeoutAt <= t
                BY <3>4b, Zenon DEF DueP
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

(* Replace one key, then a whole set of messages whose keys are fresh. *)
Post(b, msg) ==
    { x \in b : MsgKey(x) /= MsgKey(msg) } \cup {msg}

Posted(b, M) ==
    IF M = {} THEN b
    ELSE { x \in b : \A m \in M : MsgKey(x) /= MsgKey(m) } \cup M

LEMMA PostedStep ==
    ASSUME NEW b, NEW M, NEW msg,
           \A m \in M : MsgKey(m) /= MsgKey(msg)
    PROVE  Post(Posted(b, M), msg) = Posted(b, M \cup {msg})
PROOF
    <1> DEFINE p == Post(Posted(b, M), msg)
    <1> DEFINE q == Posted(b, M \cup {msg})
    <1>1. CASE M = {}
        <2>1. Posted(b, M) = b
            BY <1>1 DEF Posted
        <2>2. M \cup {msg} = {msg} /\ {msg} # {}
            BY <1>1
        <2>3. q = { x \in b : \A m \in {msg} : MsgKey(x) /= MsgKey(m) } \cup {msg}
            BY <2>2 DEF q, Posted
        <2>4. p = { x \in b : MsgKey(x) /= MsgKey(msg) } \cup {msg}
            BY <2>1 DEF p, Post
        <2>5. \A y : y \in p <=> y \in q
            BY <2>3, <2>4, Zenon
        <2>6. QED
            BY <2>5, IsaWithSetExtensionality
    <1>2. CASE M # {}
        <2> DEFINE src ==
                { x \in b : \A m \in M : MsgKey(x) /= MsgKey(m) } \cup M
        <2>1. Posted(b, M) = src
            BY <1>2 DEF Posted, src
        <2>2. M \cup {msg} # {}
            BY Z3
        <2>3. q = { x \in b : \A m \in M \cup {msg} : MsgKey(x) /= MsgKey(m) }
                    \cup (M \cup {msg})
            BY <2>2 DEF q, Posted
        <2>4. p = { x \in src : MsgKey(x) /= MsgKey(msg) } \cup {msg}
            BY <2>1 DEF p, Post
        <2>5. \A y : y \in p <=> y \in q
            BY <2>3, <2>4, Zenon DEF src
        <2>6. QED
            BY <2>5, IsaWithSetExtensionality
    <1>3. QED
        BY <1>1, <1>2

LEMMA InSwept ==
    ASSUME NEW t, NEW os, NEW b, NEW n \in 0 .. P!MaxSweep,
           ReachN(Objects, outbox, t, os, b, n)
    PROVE  Store(os, b) \in P!Swept(t)
PROOF
    <1>1. Store(os, b) \in F(Objects, outbox, t, P!MaxSweep)[P!MaxSweep]
        BY ReachIn
    <1>2. F(Objects, outbox, t, P!MaxSweep)[P!MaxSweep] = P!Swept(t)
        BY SweptIs
    <1>3. QED
        BY <1>1, <1>2

===============================================================================
