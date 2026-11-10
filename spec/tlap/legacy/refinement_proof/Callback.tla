------------------------------ MODULE Callback -----------------------------
(* A callback pass drops one (awaited, awaiter) pair. The outbox stays.
   The pass starts from a store whose projection is already the identity. *)
EXTENDS Listen

IdsC(o, t) ==
    { j \in DOMAIN o : P!Project(o[j], t).promise.state /= "pending" }

DueC(o, t) ==
    { x \in [id : IdsC(o, t), awaiter : Id] :
        x.awaiter \in o[x.id].promise.callbacks }

Src(j, S) ==
    { p.id : p \in { y \in S : y.awaiter = j } }

Drp(j, S) ==
    { p.awaiter : p \in { y \in S : y.id = j } }

Cleared(o, S, j) ==
    LET g == Drp(j, S)
    IN  IF g = {} THEN o[j]
        ELSE P!WithoutCallbacks(o[j], g)

Woken(obj, srcs, t) ==
    IF srcs = {} THEN obj
    ELSE IF obj.task.state \in {"none", "fulfilled"} THEN obj
    ELSE IF obj.task.state = "suspended" THEN
        P!WakeSuspended(obj, srcs, t)
    ELSE
        P!UnionResumes(obj, srcs)

BodyC(o, S, j, t) ==
    Woken(Cleared(o, S, j), Src(j, S), t)

ImgC(o, S, t) ==
    IF S = {} THEN o
    ELSE [ j \in DOMAIN o |-> BodyC(o, S, j, t) ]

LEMMA RecAw ==
    ASSUME NEW U, NEW x \in [id : U, awaiter : Id]
    PROVE  x = [id |-> x.id, awaiter |-> x.awaiter]
PROOF
    BY Isa

LEMMA ProjectClear ==
    ASSUME NEW obj, NEW t, NEW obj2, NEW G,
           P!Project(obj, t) = obj,
           obj2 = P!WithoutCallbacks(obj, G)
    PROVE  P!Project(obj2, t) = obj2
PROOF
    <1>1. \/ obj.promise.state /= "pending"
          \/ ~(obj.promise.timeoutAt <= t)
        BY GuardHeld
    <1>2. /\ obj2.promise.state = obj.promise.state
          /\ obj2.promise.timeoutAt = obj.promise.timeoutAt
        BY DEF P!WithoutCallbacks
    <1>3. \/ obj2.promise.state /= "pending"
          \/ ~(obj2.promise.timeoutAt <= t)
        BY <1>1, <1>2
    <1>4. QED
        BY <1>3, ProjectId

LEMMA ClearDrop ==
    ASSUME NEW obj, NEW G, NEW a
    PROVE  P!WithoutCallbacks(P!WithoutCallbacks(obj, G), {a})
              = P!WithoutCallbacks(obj, G \cup {a})
PROOF
    BY Zenon DEF P!WithoutCallbacks

LEMMA WakeAdd ==
    ASSUME NEW obj, NEW srcs, NEW i, NEW t
    PROVE  /\ P!UnionResumes(P!UnionResumes(obj, srcs), {i})
                = P!UnionResumes(obj, srcs \cup {i})
           /\ P!UnionResumes(P!WakeSuspended(obj, srcs, t), {i})
                = P!WakeSuspended(obj, srcs \cup {i}, t)
PROOF
    BY Zenon DEF P!UnionResumes, P!WakeSuspended

LEMMA DrpStep ==
    ASSUME NEW j, NEW S, NEW x,
           x = [id |-> x.id, awaiter |-> x.awaiter]
    PROVE  Drp(j, S \cup {x})
              = IF j = x.id THEN Drp(j, S) \cup {x.awaiter} ELSE Drp(j, S)
PROOF
    <1>1. CASE j = x.id
        <2>1. \A a : a \in Drp(j, S \cup {x}) <=> a \in Drp(j, S) \cup {x.awaiter}
            <3> SUFFICES ASSUME NEW a
                         PROVE  a \in Drp(j, S \cup {x})
                                  <=> a \in Drp(j, S) \cup {x.awaiter}
                OBVIOUS
            <3>1. a \in Drp(j, S \cup {x})
                    <=> \E p \in S \cup {x} : p.id = j /\ p.awaiter = a
                BY DEF Drp
            <3>2. a \in Drp(j, S)
                    <=> \E p \in S : p.id = j /\ p.awaiter = a
                BY DEF Drp
            <3>3. QED
                BY <1>1, <3>1, <3>2, Z3
        <2>2. QED
            BY <1>1, <2>1, SetExtensionality
    <1>2. CASE j /= x.id
        <2>1. \A a : a \in Drp(j, S \cup {x}) <=> a \in Drp(j, S)
            <3> SUFFICES ASSUME NEW a
                         PROVE  a \in Drp(j, S \cup {x}) <=> a \in Drp(j, S)
                OBVIOUS
            <3>1. a \in Drp(j, S \cup {x})
                    <=> \E p \in S \cup {x} : p.id = j /\ p.awaiter = a
                BY DEF Drp
            <3>2. a \in Drp(j, S)
                    <=> \E p \in S : p.id = j /\ p.awaiter = a
                BY DEF Drp
            <3>3. x.id /= j
                BY <1>2
            <3>4. QED
                BY <3>1, <3>2, <3>3, Z3
        <2>2. QED
            BY <1>2, <2>1, SetExtensionality
    <1>3. QED
        BY <1>1, <1>2

LEMMA SrcStep ==
    ASSUME NEW j, NEW S, NEW x,
           x = [id |-> x.id, awaiter |-> x.awaiter]
    PROVE  Src(j, S \cup {x})
              = IF j = x.awaiter THEN Src(j, S) \cup {x.id} ELSE Src(j, S)
PROOF
    <1>1. CASE j = x.awaiter
        <2>1. \A a : a \in Src(j, S \cup {x}) <=> a \in Src(j, S) \cup {x.id}
            <3> SUFFICES ASSUME NEW a
                         PROVE  a \in Src(j, S \cup {x})
                                  <=> a \in Src(j, S) \cup {x.id}
                OBVIOUS
            <3>1. a \in Src(j, S \cup {x})
                    <=> \E p \in S \cup {x} : p.awaiter = j /\ p.id = a
                BY DEF Src
            <3>2. a \in Src(j, S)
                    <=> \E p \in S : p.awaiter = j /\ p.id = a
                BY DEF Src
            <3>3. QED
                BY <1>1, <3>1, <3>2, Z3
        <2>2. QED
            BY <1>1, <2>1, SetExtensionality
    <1>2. CASE j /= x.awaiter
        <2>1. \A a : a \in Src(j, S \cup {x}) <=> a \in Src(j, S)
            <3> SUFFICES ASSUME NEW a
                         PROVE  a \in Src(j, S \cup {x}) <=> a \in Src(j, S)
                OBVIOUS
            <3>1. a \in Src(j, S \cup {x})
                    <=> \E p \in S \cup {x} : p.awaiter = j /\ p.id = a
                BY DEF Src
            <3>2. a \in Src(j, S)
                    <=> \E p \in S : p.awaiter = j /\ p.id = a
                BY DEF Src
            <3>3. x.awaiter /= j
                BY <1>2
            <3>4. QED
                BY <3>1, <3>2, <3>3, Z3
        <2>2. QED
            BY <1>2, <2>1, SetExtensionality
    <1>3. QED
        BY <1>1, <1>2

LEMMA CallAt ==
    ASSUME NEW o, NEW S, NEW j, NEW t,
           j \in DOMAIN o
    PROVE  /\ j \in DOMAIN ImgC(o, S, t)
           /\ ImgC(o, S, t)[j] = BodyC(o, S, j, t)
PROOF
    <1>1. CASE S = {}
        <2>1. Drp(j, S) = {} /\ Src(j, S) = {}
            BY <1>1 DEF Drp, Src
        <2>2. BodyC(o, S, j, t) = o[j]
            BY <2>1 DEF BodyC, Cleared, Woken
        <2>3. QED
            BY <1>1, <2>2 DEF ImgC
    <1>2. CASE S # {}
        <2> DEFINE fn == [ k \in DOMAIN o |-> BodyC(o, S, k, t) ]
        <2>1. ImgC(o, S, t) = fn
            BY <1>2 DEF ImgC, fn
        <2>2. DOMAIN fn = DOMAIN o
            BY DomCtor DEF fn
        <2>3. QED
            BY <1>2, <2>1, <2>2, Z3 DEF fn
    <1>3. QED
        BY <1>1, <1>2

LEMMA AwFinite ==
    ASSUME NEW base, NEW t, DOMAIN base \subseteq Id
    PROVE  IsFiniteSet(DueC(base, t))
PROOF
    <1> DEFINE Op(p) == [id |-> p[1], awaiter |-> p[2]]
    <1> DEFINE Img == { Op(p) : p \in Id \X Id }
    <1>1. IsFiniteSet(Id)
        BY FiniteOrigin, FiniteRest, FiniteAddress, IdFinite
    <1>2. IsFiniteSet(Id \X Id)
        BY <1>1, FS_Product
    <1>3. LET T == { Op(x) : x \in Id \X Id }
          IN  IsFiniteSet(T)
        BY <1>2, FS_Image
    <1>4. IsFiniteSet(Img)
        BY <1>3 DEF Img
    <1>5. DueC(base, t) \subseteq Img
        <2> SUFFICES ASSUME NEW x \in DueC(base, t)
                     PROVE  x \in Img
            OBVIOUS
        <2>1. x \in [id : DOMAIN base, awaiter : Id]
            BY DEF DueC, IdsC
        <2>2. x.id \in DOMAIN base /\ x.awaiter \in Id
            BY <2>1, Z3
        <2>3. x.id \in Id
            BY <2>2
        <2> DEFINE p == <<x.id, x.awaiter>>
        <2>4. p \in Id \X Id
            BY <2>2, <2>3, PairIn DEF p
        <2>5. x = Op(p)
            BY <2>1, RecAw, Isa DEF Op, p
        <2>6. QED
            BY <2>4, <2>5 DEF Img
    <1>6. QED
        BY <1>4, <1>5, FS_Subset

LEMMA InDue1C ==
    ASSUME NEW o, NEW b, NEW t, NEW st \in P!DueCallback(o, b, t)
    PROVE  st \in D1(o, b, t)
PROOF
    BY DEF D1, P!Due1

LEMMA BodyPromise ==
    ASSUME NEW o, NEW S, NEW j \in DOMAIN o, NEW t
    PROVE  /\ BodyC(o, S, j, t).promise.state = o[j].promise.state
           /\ BodyC(o, S, j, t).promise.timeoutAt = o[j].promise.timeoutAt
           /\ BodyC(o, S, j, t).promise.callbacks
                = o[j].promise.callbacks \ Drp(j, S)
PROOF
    <1> DEFINE g == Drp(j, S)
    <1> DEFINE srcs == Src(j, S)
    <1> DEFINE cleared == Cleared(o, S, j)
    <1> DEFINE goal(obj) ==
            /\ obj.promise.state = o[j].promise.state
            /\ obj.promise.timeoutAt = o[j].promise.timeoutAt
            /\ obj.promise.callbacks = o[j].promise.callbacks \ g
    <1>1. CASE g = {}
        <2>1. cleared = o[j]
            BY <1>1 DEF cleared, Cleared, g
        <2>2. o[j].promise.callbacks \ g = o[j].promise.callbacks
            BY <1>1 DEF g
        <2>3. CASE srcs = {}
            BY <2>1, <2>2, <2>3 DEF BodyC, Woken, cleared, srcs, goal
        <2>4. CASE srcs # {} /\ o[j].task.state \in {"none", "fulfilled"}
            BY <2>1, <2>2, <2>4 DEF BodyC, Woken, cleared, srcs, goal
        <2>5. CASE srcs # {} /\ o[j].task.state = "suspended"
            BY <2>1, <2>2, <2>5 DEF BodyC, Woken, P!WakeSuspended, cleared, srcs, goal
        <2>6. CASE srcs # {} /\ o[j].task.state \notin {"none", "fulfilled", "suspended"}
            BY <2>1, <2>2, <2>6 DEF BodyC, Woken, P!UnionResumes, cleared, srcs, goal
        <2>7. QED
            BY <2>3, <2>4, <2>5, <2>6
    <1>2. CASE g # {}
        <2>1. cleared = P!WithoutCallbacks(o[j], g)
            BY <1>2 DEF cleared, Cleared, g
        <2>2. goal(cleared)
            BY <2>1 DEF goal, P!WithoutCallbacks
        <2>3. CASE srcs = {}
            BY <2>2, <2>3 DEF BodyC, Woken, cleared, srcs, goal
        <2>4. CASE srcs # {} /\ cleared.task.state \in {"none", "fulfilled"}
            BY <2>1, <2>2, <2>4 DEF BodyC, Woken, cleared, srcs, goal, P!WithoutCallbacks
        <2>5. CASE srcs # {} /\ cleared.task.state = "suspended"
            BY <2>2, <2>5 DEF BodyC, Woken, P!WakeSuspended, cleared, srcs, goal
        <2>6. CASE srcs # {} /\ cleared.task.state \notin {"none", "fulfilled", "suspended"}
            BY <2>2, <2>6 DEF BodyC, Woken, P!UnionResumes, cleared, srcs, goal
        <2>7. QED
            BY <2>3, <2>4, <2>5, <2>6
    <1>3. QED
        BY <1>1, <1>2 DEF goal

LEMMA CallMember ==
    ASSUME NEW o, NEW b, NEW t, NEW i \in DOMAIN o, NEW w,
           w \in o[i].promise.callbacks,
           P!Project(o[i], t) = o[i],
           o[i].promise.state /= "pending"
    PROVE  Store(P!CallbackObjects(o, i, w, t), b) \in P!DueCallback(o, b, t)
PROOF
    <1> DEFINE ids ==
            { j \in DOMAIN o : P!Project(o[j], t).promise.state /= "pending" }
    <1> DEFINE pack(j, ww) ==
            [ objects |-> P!CallbackObjects(o, j, ww, t),
              outbox  |-> b ]
    <1> DEFINE fam ==
            { { pack(j, ww) : ww \in o[j].promise.callbacks } : j \in ids }
    <1> DEFINE rec ==
            [ objects |-> P!CallbackObjects(o, i, w, t),
              outbox  |-> b ]
    <1>1. i \in ids /\ ids # {}
        BY DEF ids
    <1>2. Store(P!CallbackObjects(o, i, w, t), b) = rec
        BY DEF rec, Store
    <1>3. rec = pack(i, w)
        BY DEF rec, pack
    <1>4. pack(i, w) \in { pack(i, ww) : ww \in o[i].promise.callbacks }
        BY Zenon DEF pack
    <1>5. { pack(i, ww) : ww \in o[i].promise.callbacks } \in fam
        BY <1>1, Zenon DEF fam
    <1>6. pack(i, w) \in UNION fam
        BY <1>4, <1>5, Zenon
    <1>7. P!DueCallback(o, b, t) = UNION fam
        BY <1>1, Zenon DEF fam, pack, ids, P!DueCallback
    <1>8. QED
        BY <1>2, <1>3, <1>6, <1>7

LEMMA WriteAt ==
    ASSUME NEW doc, NEW id, NEW obj, NEW k,
           k \in (DOMAIN doc) \cup {id}
    PROVE  P!Write(doc, id, obj)[k] = IF k = id THEN obj ELSE doc[k]
PROOF
    BY Zenon DEF P!Write

LEMMA WriteDom ==
    ASSUME NEW doc, NEW id, NEW obj
    PROVE  DOMAIN P!Write(doc, id, obj) = (DOMAIN doc) \cup {id}
PROOF
    BY DomCtor DEF P!Write

LEMMA ClearWake ==
    ASSUME NEW obj, NEW a, NEW srcs, NEW t
    PROVE  /\ P!WithoutCallbacks(P!WakeSuspended(obj, srcs, t), {a})
                = P!WakeSuspended(P!WithoutCallbacks(obj, {a}), srcs, t)
           /\ P!WithoutCallbacks(P!UnionResumes(obj, srcs), {a})
                = P!UnionResumes(P!WithoutCallbacks(obj, {a}), srcs)
PROOF
    BY Zenon DEF P!WithoutCallbacks, P!WakeSuspended, P!UnionResumes

===============================================================================

