------------------------------- MODULE Listen ------------------------------
(* A listener pass drops one (id, address) pair and posts one Unblock.
   The pass starts from a store whose projection is already the identity,
   which is what the timeout pass leaves behind. *)
EXTENDS Retry

Ids(o, t) ==
    { j \in DOMAIN o : P!Project(o[j], t).promise.state /= "pending" }

DueN(o, t) ==
    { x \in [id : Ids(o, t), address : Address] :
        x.address \in o[x.id].promise.listeners }

Struck(obj, G) ==
    [ promise |-> [ state     |-> obj.promise.state,
                    param     |-> obj.promise.param,
                    value     |-> obj.promise.value,
                    tags      |-> obj.promise.tags,
                    timeoutAt |-> obj.promise.timeoutAt,
                    createdAt |-> obj.promise.createdAt,
                    settledAt |-> obj.promise.settledAt,
                    callbacks |-> obj.promise.callbacks,
                    listeners |-> obj.promise.listeners \ G ],
      task    |-> obj.task ]

LBody(obj, a) ==
    Struck(obj, {a})

UnblockMsg(o, i, a, t) ==
    [ address |-> a,
      message |-> [ tag   |-> "Unblock",
                    id    |-> i,
                    state |-> P!Project(o[i], t).promise.state ] ]

Gone(i, P) ==
    { addr \in Address : [id |-> i, address |-> addr] \in P }

BodyN(o, P, i) ==
    LET g == Gone(i, P)
    IN  IF g = {} THEN o[i]
        ELSE Struck(o[i], g)

ImgN(o, P) ==
    IF P = {} THEN o
    ELSE [ j \in DOMAIN o |-> BodyN(o, P, j) ]

MsgN(o, P, t) ==
    { UnblockMsg(o, p.id, p.address, t) : p \in P }

BoxN(b, o, P, t) ==
    Posted(b, MsgN(o, P, t))

LEMMA SameMsgKey ==
    ASSUME NEW e
    PROVE  MsgKey(e) = P!MsgKey(e)
PROOF
    BY DEF MsgKey, P!MsgKey

LEMMA GuardHeld ==
    ASSUME NEW obj, NEW t, P!Project(obj, t) = obj
    PROVE  \/ obj.promise.state /= "pending"
           \/ ~(obj.promise.timeoutAt <= t)
PROOF
    <1>1. CASE obj.promise.state = "pending" /\ obj.promise.timeoutAt <= t
        <2> DEFINE p == P!Project(obj, t)
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
        <2>4. p.promise.state /= "pending"
            BY <2>1, <2>2, <2>3
        <2>5. QED
            BY <1>1, <2>4 DEF p
    <1>2. QED
        BY <1>1

LEMMA ProjectDrop ==
    ASSUME NEW obj, NEW t, NEW obj2, NEW G,
           P!Project(obj, t) = obj,
           obj2 = Struck(obj, G)
    PROVE  P!Project(obj2, t) = obj2
PROOF
    <1>1. \/ obj.promise.state /= "pending"
          \/ ~(obj.promise.timeoutAt <= t)
        BY GuardHeld
    <1>2. /\ obj2.promise.state = obj.promise.state
          /\ obj2.promise.timeoutAt = obj.promise.timeoutAt
        BY DEF Struck
    <1>3. \/ obj2.promise.state /= "pending"
          \/ ~(obj2.promise.timeoutAt <= t)
        BY <1>1, <1>2
    <1>4. QED
        BY <1>3, ProjectId

LEMMA RecPair ==
    ASSUME NEW S, NEW x \in [id : S, address : Address]
    PROVE  x = [id |-> x.id, address |-> x.address]
PROOF
    BY Isa

LEMMA SameStruck ==
    ASSUME NEW obj, NEW G
    PROVE  Struck(obj, G) = P!WithoutListeners(obj, G)
PROOF
    BY DEF Struck, P!WithoutListeners

LEMMA StruckDrop ==
    ASSUME NEW obj, NEW G, NEW a
    PROVE  Struck(Struck(obj, G), {a}) = Struck(obj, G \cup {a})
PROOF
    BY Zenon DEF Struck

LEMMA ListenMember ==
    ASSUME NEW o, NEW b, NEW t, NEW i \in DOMAIN o, NEW a \in Address,
           a \in o[i].promise.listeners,
           P!Project(o[i], t) = o[i],
           o[i].promise.state /= "pending"
    PROVE  Store(P!Write(o, i, LBody(o[i], a)), Post(b, UnblockMsg(o, i, a, t)))
              \in P!DueListener(o, b, t)
PROOF
    <1> DEFINE awaited == o[i]
    <1> DEFINE msg ==
            [ address |-> a,
              message |-> [ tag   |-> "Unblock",
                            id    |-> i,
                            state |-> awaited.promise.state ] ]
    <1>1. P!Project(o[i], t) = awaited
        BY DEF awaited
    <1>2. UnblockMsg(o, i, a, t) = msg
        BY <1>1 DEF UnblockMsg, msg
    <1>3. LBody(o[i], a) = P!WithoutListeners(awaited, {a})
        BY SameStruck DEF LBody, awaited
    <1>4. \A e : MsgKey(e) = P!MsgKey(e)
        BY SameMsgKey
    <1>5. Post(b, msg) = { x \in b : P!MsgKey(x) /= P!MsgKey(msg) } \cup {msg}
        <2>1. \A y : y \in Post(b, msg)
                       <=> y \in { x \in b : P!MsgKey(x) /= P!MsgKey(msg) } \cup {msg}
            BY <1>4, Zenon DEF Post
        <2>2. QED
            BY <2>1, SetExtensionality
    <1>6. Store(P!Write(o, i, P!WithoutListeners(awaited, {a})),
                { x \in b : P!MsgKey(x) /= P!MsgKey(msg) } \cup {msg})
            \in P!DueListener(o, b, t)
        <2> DEFINE ids ==
                { j \in DOMAIN o : P!Project(o[j], t).promise.state /= "pending" }
        <2> DEFINE rec ==
                [ objects |-> P!Write(o, i, P!WithoutListeners(awaited, {a})),
                  outbox  |-> { kept \in b : P!MsgKey(kept) /= P!MsgKey(msg) } \cup {msg} ]
        <2> DEFINE pack(j, aa) ==
                LET aw == P!Project(o[j], t)
                    m  == [ address |-> aa,
                            message |-> [ tag   |-> "Unblock",
                                          id    |-> j,
                                          state |-> aw.promise.state ] ]
                IN  [ objects |-> P!Write(o, j, P!WithoutListeners(aw, {aa})),
                      outbox  |-> { kept \in b : P!MsgKey(kept) /= P!MsgKey(m) } \cup {m} ]
        <2> DEFINE fam ==
                { { pack(j, aa) : aa \in o[j].promise.listeners } : j \in ids }
        <2>1. P!Project(o[i], t).promise.state /= "pending"
            BY <1>1 DEF awaited
        <2>2. i \in ids /\ ids /= {}
            BY <2>1 DEF ids
        <2>3. { x \in b : P!MsgKey(x) /= P!MsgKey(msg) }
                = { kept \in b : P!MsgKey(kept) /= P!MsgKey(msg) }
            <3>1. \A y : y \in { x \in b : P!MsgKey(x) /= P!MsgKey(msg) }
                         <=> y \in { kept \in b : P!MsgKey(kept) /= P!MsgKey(msg) }
                BY Zenon
            <3>2. QED
                BY <3>1, SetExtensionality
        <2>4. Store(P!Write(o, i, P!WithoutListeners(awaited, {a})),
                    { x \in b : P!MsgKey(x) /= P!MsgKey(msg) } \cup {msg})
                = rec
            BY <2>3 DEF rec, Store
        <2>5. rec = pack(i, a)
            BY <1>1, Zenon DEF rec, pack, msg, awaited
        <2>6. pack(i, a) \in { pack(i, aa) : aa \in o[i].promise.listeners }
            BY Zenon DEF pack
        <2>7. { pack(i, aa) : aa \in o[i].promise.listeners } \in fam
            BY <2>2, Zenon DEF fam
        <2>8. pack(i, a) \in UNION fam
            BY <2>6, <2>7, Zenon
        <2>9. P!DueListener(o, b, t) = UNION fam
            BY <2>2, Zenon DEF fam, pack, ids, P!DueListener
        <2>10. QED
            BY <2>4, <2>5, <2>8, <2>9
    <1>7. QED
        BY <1>2, <1>3, <1>5, <1>6

LEMMA InDue1N ==
    ASSUME NEW o, NEW b, NEW t, NEW st \in P!DueListener(o, b, t)
    PROVE  st \in D1(o, b, t)
PROOF
    BY DEF D1, P!Due1

LEMMA UnblockKey ==
    ASSUME NEW o, NEW t, NEW x, NEW y,
           x \in [id : DOMAIN o, address : Address],
           y \in [id : DOMAIN o, address : Address],
           x /= y
    PROVE  MsgKey(UnblockMsg(o, x.id, x.address, t))
              /= MsgKey(UnblockMsg(o, y.id, y.address, t))
PROOF
    BY RecPair, Zenon DEF MsgKey, UnblockMsg

LEMMA PairSubset ==
    ASSUME NEW o, NEW t
    PROVE  DueN(o, t) \subseteq [id : DOMAIN o, address : Address]
PROOF
    BY DEF DueN, Ids

LEMMA PairFinite ==
    ASSUME NEW base, NEW t, DOMAIN base \subseteq Id
    PROVE  IsFiniteSet(DueN(base, t))
PROOF
    <1> DEFINE Op(p) == [id |-> p[1], address |-> p[2]]
    <1> DEFINE Img == { Op(p) : p \in Id \X Address }
    <1>1. IsFiniteSet(Id) /\ IsFiniteSet(Address)
        BY FiniteOrigin, FiniteRest, FiniteAddress, IdFinite
    <1>2. IsFiniteSet(Id \X Address)
        BY <1>1, FS_Product
    <1>3. LET T == { Op(x) : x \in Id \X Address }
          IN  IsFiniteSet(T)
        BY <1>2, FS_Image
    <1>4. IsFiniteSet(Img)
        BY <1>3 DEF Img
    <1>5. DueN(base, t) \subseteq Img
        <2> SUFFICES ASSUME NEW x \in DueN(base, t)
                     PROVE  x \in Img
            OBVIOUS
        <2>1. x \in [id : DOMAIN base, address : Address]
            BY PairSubset
        <2>2. x.id \in DOMAIN base /\ x.address \in Address
            BY <2>1, Z3
        <2>3. x.id \in Id
            BY <2>2
        <2> DEFINE p == <<x.id, x.address>>
        <2>4. p \in Id \X Address
            BY <2>2, <2>3, PairIn DEF p
        <2>5. x = Op(p)
            BY <2>1, RecPair, Isa DEF Op, p
        <2>6. QED
            BY <2>4, <2>5 DEF Img
    <1>6. QED
        BY <1>4, <1>5, FS_Subset

LEMMA MsgUnionN ==
    ASSUME NEW o, NEW P, NEW x, NEW t,
           x \notin P
    PROVE  MsgN(o, P \cup {x}, t) = MsgN(o, P, t) \cup {UnblockMsg(o, x.id, x.address, t)}
PROOF
    <1>1. \A y : y \in MsgN(o, P \cup {x}, t)
                 <=> y \in MsgN(o, P, t) \cup {UnblockMsg(o, x.id, x.address, t)}
        BY Zenon DEF MsgN
    <1>2. QED
        BY <1>1, IsaWithSetExtensionality

LEMMA FreshKeyN ==
    ASSUME NEW o, NEW P, NEW x, NEW t,
           x \notin P,
           x \in [id : DOMAIN o, address : Address],
           P \subseteq [id : DOMAIN o, address : Address]
    PROVE  \A m \in MsgN(o, P, t) :
              MsgKey(m) /= MsgKey(UnblockMsg(o, x.id, x.address, t))
PROOF
    <1> SUFFICES ASSUME NEW m \in MsgN(o, P, t)
                 PROVE  MsgKey(m) /= MsgKey(UnblockMsg(o, x.id, x.address, t))
        OBVIOUS
    <1>1. \E p \in P : m = UnblockMsg(o, p.id, p.address, t)
        BY DEF MsgN
    <1>2. PICK p \in P : m = UnblockMsg(o, p.id, p.address, t)
        BY <1>1
    <1>3. p /= x /\ p \in [id : DOMAIN o, address : Address]
        BY <1>2
    <1>4. QED
        BY <1>2, <1>3, UnblockKey

LEMMA BoxStepN ==
    ASSUME NEW b, NEW o, NEW P, NEW x, NEW t,
           x \notin P,
           x \in [id : DOMAIN o, address : Address],
           P \subseteq [id : DOMAIN o, address : Address]
    PROVE  Post(BoxN(b, o, P, t), UnblockMsg(o, x.id, x.address, t))
              = BoxN(b, o, P \cup {x}, t)
PROOF
    <1>1. \A m \in MsgN(o, P, t) :
              MsgKey(m) /= MsgKey(UnblockMsg(o, x.id, x.address, t))
        BY FreshKeyN
    <1>2. Post(Posted(b, MsgN(o, P, t)), UnblockMsg(o, x.id, x.address, t))
            = Posted(b, MsgN(o, P, t) \cup {UnblockMsg(o, x.id, x.address, t)})
        BY <1>1, PostedStep
    <1>3. MsgN(o, P, t) \cup {UnblockMsg(o, x.id, x.address, t)}
            = MsgN(o, P \cup {x}, t)
        BY MsgUnionN
    <1>4. QED
        BY <1>2, <1>3 DEF BoxN

LEMMA ListenAt ==
    ASSUME NEW o, NEW P, NEW i,
           i \in DOMAIN o, P \subseteq [id : DOMAIN o, address : Address]
    PROVE  /\ i \in DOMAIN ImgN(o, P)
           /\ ImgN(o, P)[i] = BodyN(o, P, i)
PROOF
    <1>1. CASE P = {}
        <2>1. Gone(i, P) = {}
            BY <1>1 DEF Gone
        <2>2. BodyN(o, P, i) = o[i]
            BY <2>1 DEF BodyN
        <2>3. QED
            BY <1>1, <2>2 DEF ImgN
    <1>2. CASE P # {}
        <2> DEFINE fn == [ j \in DOMAIN o |-> BodyN(o, P, j) ]
        <2>1. ImgN(o, P) = fn
            BY <1>2 DEF ImgN, fn
        <2>2. DOMAIN fn = DOMAIN o
            BY DomCtor DEF fn
        <2>3. QED
            BY <1>2, <2>1, <2>2, Z3 DEF fn
    <1>3. QED
        BY <1>1, <1>2

LEMMA GoneStep ==
    ASSUME NEW i, NEW R, NEW x,
           x = [id |-> x.id, address |-> x.address],
           x.address \in Address
    PROVE  Gone(i, R \cup {x})
              = IF i = x.id THEN Gone(i, R) \cup {x.address} ELSE Gone(i, R)
PROOF
    <1>1. CASE i = x.id
        <2>1. \A addr :
                addr \in Gone(i, R \cup {x})
                  <=> addr \in Gone(i, R) \cup {x.address}
            <3> SUFFICES ASSUME NEW addr
                         PROVE  addr \in Gone(i, R \cup {x})
                                  <=> addr \in Gone(i, R) \cup {x.address}
                OBVIOUS
            <3>1. addr \in Gone(i, R \cup {x})
                    <=> addr \in Address /\ [id |-> i, address |-> addr] \in R \cup {x}
                BY DEF Gone
            <3>2. addr \in Gone(i, R)
                    <=> addr \in Address /\ [id |-> i, address |-> addr] \in R
                BY DEF Gone
            <3>3. [id |-> i, address |-> addr] = x <=> addr = x.address
                BY <1>1
            <3>4. QED
                BY <1>1, <3>1, <3>2, <3>3, Z3
        <2>2. QED
            BY <1>1, <2>1, SetExtensionality
    <1>2. CASE i /= x.id
        <2>1. \A addr :
                addr \in Gone(i, R \cup {x}) <=> addr \in Gone(i, R)
            <3> SUFFICES ASSUME NEW addr
                         PROVE  addr \in Gone(i, R \cup {x}) <=> addr \in Gone(i, R)
                OBVIOUS
            <3>1. addr \in Gone(i, R \cup {x})
                    <=> addr \in Address /\ [id |-> i, address |-> addr] \in R \cup {x}
                BY DEF Gone
            <3>2. addr \in Gone(i, R)
                    <=> addr \in Address /\ [id |-> i, address |-> addr] \in R
                BY DEF Gone
            <3>3. [id |-> i, address |-> addr] /= x
                BY <1>2
            <3>4. QED
                BY <1>2, <3>1, <3>2, <3>3, Z3
        <2>2. QED
            BY <1>2, <2>1, SetExtensionality
    <1>3. QED
        BY <1>1, <1>2

LEMMA ListenBulk ==
    ASSUME NEW o, NEW S, NEW x, NEW prev, NEW i, NEW a,
           x \notin S,
           x \in [id : DOMAIN o, address : Address],
           S \subseteq [id : DOMAIN o, address : Address],
           prev = ImgN(o, S),
           i = x.id,
           a = x.address
    PROVE  P!Write(prev, i, LBody(prev[i], a)) = ImgN(o, S \cup {x})
PROOF
    <1>1. x = [id |-> x.id, address |-> x.address]
        BY RecPair
    <1>2. x.id \in DOMAIN o /\ x.address \in Address
        BY Z3
    <1>2b. i \in DOMAIN o /\ a \in Address
        BY <1>2
    <1> DEFINE nxt == ImgN(o, S \cup {x})
    <1> DEFINE body == LBody(prev[i], a)
    <1>3. i \in DOMAIN prev /\ prev[i] = BodyN(o, S, i)
        BY <1>2b, ListenAt, Z3
    <1>4. S \cup {x} # {}
        BY Z3
    <1>5. nxt = [ k \in DOMAIN o |-> BodyN(o, S \cup {x}, k) ]
        BY <1>4 DEF nxt, ImgN
    <1>6. P!Write(prev, i, body)
            = [ k \in DOMAIN o |-> IF k = i THEN body ELSE prev[k] ]
        <2> DEFINE e(k) == IF k = i THEN body ELSE prev[k]
        <2>1. P!Write(prev, i, body)
                = [ k \in (DOMAIN prev) \cup {i} |-> e(k) ]
            BY DEF e, body, P!Write
        <2>2. (DOMAIN prev) \cup {i} = DOMAIN o
            <3>1. DOMAIN prev = DOMAIN o
                <4>1. CASE S = {}
                    BY <4>1 DEF ImgN
                <4>2. CASE S # {}
                    <5> DEFINE fn == [ j \in DOMAIN o |-> BodyN(o, S, j) ]
                    <5>1. prev = fn
                        BY <4>2 DEF ImgN, fn
                    <5>2. DOMAIN fn = DOMAIN o
                        BY DomCtor DEF fn
                    <5>3. QED
                        BY <5>1, <5>2
                <4>3. QED
                    BY <4>1, <4>2
            <3>2. \A y : y \in (DOMAIN prev) \cup {i} <=> y \in DOMAIN o
                BY <1>2b, <3>1, Z3
            <3>3. QED
                BY <3>2, IsaWithSetExtensionality
        <2>3. \A k \in DOMAIN o : e(k) = IF k = i THEN body ELSE prev[k]
            BY DEF e
        <2>4. QED
            BY <2>1, <2>2, <2>3, ExtCtor
    <1>7. \A k \in DOMAIN o :
            (IF k = i THEN LBody(prev[k], a) ELSE prev[k])
              = BodyN(o, S \cup {x}, k)
        <2> SUFFICES ASSUME NEW k \in DOMAIN o
                     PROVE  (IF k = i THEN LBody(prev[k], a) ELSE prev[k])
                               = BodyN(o, S \cup {x}, k)
            OBVIOUS
        <2>1. prev[k] = BodyN(o, S, k)
            BY <1>2b, ListenAt, Z3
        <2>2. Gone(k, S \cup {x})
                = IF k = x.id THEN Gone(k, S) \cup {x.address} ELSE Gone(k, S)
            BY <1>1, <1>2, GoneStep
        <2>2b. Gone(k, S \cup {x})
                = IF k = i THEN Gone(k, S) \cup {a} ELSE Gone(k, S)
            BY <2>2
        <2>3. CASE k /= i
            BY <2>1, <2>2b, <2>3, Z3 DEF BodyN
        <2>4. CASE k = i
            <3>1. CASE Gone(k, S) = {}
                <4>1. prev[k] = o[k]
                    BY <2>1, <3>1 DEF BodyN
                <4>2. LBody(prev[k], a) = Struck(o[k], {a})
                    BY <4>1 DEF LBody
                <4>3. Gone(k, S \cup {x}) = {a} /\ Gone(k, S \cup {x}) # {}
                    BY <2>2b, <2>4, <3>1, Z3
                <4>4. BodyN(o, S \cup {x}, k) = Struck(o[k], {a})
                    BY <4>3 DEF BodyN
                <4>5. QED
                    BY <2>4, <4>2, <4>4, Z3
            <3>2. CASE Gone(k, S) # {}
                <4>1. prev[k] = Struck(o[k], Gone(k, S))
                    BY <2>1, <3>2 DEF BodyN
                <4>2. LBody(prev[k], a)
                        = Struck(o[k], Gone(k, S) \cup {a})
                    BY <4>1, StruckDrop DEF LBody
                <4>3. Gone(k, S \cup {x}) = Gone(k, S) \cup {a}
                    BY <2>2b, <2>4
                <4>4. Gone(k, S \cup {x}) # {}
                    BY <4>3, Z3
                <4>5. BodyN(o, S \cup {x}, k) = Struck(o[k], Gone(k, S \cup {x}))
                    BY <4>4 DEF BodyN
                <4>6. QED
                    BY <2>4, <4>2, <4>3, <4>5, Z3
            <3>3. QED
                BY <3>1, <3>2
        <2>5. QED
            BY <2>3, <2>4
    <1>8. \A k \in DOMAIN o :
            (IF k = i THEN body ELSE prev[k]) = BodyN(o, S \cup {x}, k)
        BY <1>3, <1>7, Z3 DEF body
    <1>9. P!Write(prev, i, body) = nxt
        BY <1>5, <1>6, <1>8, ExtCtor
    <1>10. QED
        BY <1>9 DEF nxt, body

LEMMA ListenReach ==
    ASSUME NEW base, NEW box, NEW t,
           DOMAIN base \subseteq Id,
           \A i \in DOMAIN base : P!Project(base[i], t) = base[i]
    PROVE  ReachN(base, box, t,
                  ImgN(base, DueN(base, t)),
                  BoxN(box, base, DueN(base, t), t),
                  Cardinality(DueN(base, t)))
PROOF
    <1> DEFINE Due == DueN(base, t)
    <1> DEFINE Closed(T) ==
            \/ T \notin SUBSET Due
            \/ ReachN(base, box, t, ImgN(base, T), BoxN(box, base, T, t),
                      Cardinality(T))
    <1>1. IsFiniteSet(Due)
        BY PairFinite DEF Due
    <1>2. Closed({})
        <2>1. ImgN(base, {}) = base
            BY DEF ImgN
        <2>2. BoxN(box, base, {}, t) = box
            <3>1. MsgN(base, {}, t) = {}
                BY DEF MsgN
            <3>2. QED
                BY <3>1 DEF BoxN, Posted
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
                  /\ T \subseteq [id : DOMAIN base, address : Address]
                  /\ x \in [id : DOMAIN base, address : Address]
                BY <1>3, <2>2, PairSubset, Z3 DEF Due
            <3>2. ReachN(base, box, t, ImgN(base, T), BoxN(box, base, T, t),
                         Cardinality(T))
                BY <1>3, <3>1, Z3 DEF Closed
            <3>3. Cardinality(T) \in Nat
                    /\ Cardinality(T \cup {x}) = Cardinality(T) + 1
                BY <1>3, FS_CardinalityType, FS_AddElement, Z3
            <3> DEFINE cur == ImgN(base, T)
            <3> DEFINE curb == BoxN(box, base, T, t)
            <3> DEFINE i == x.id
            <3> DEFINE a == x.address
            <3>4. i \in DOMAIN base /\ a \in Address /\ i \in Ids(base, t)
                    /\ a \in base[i].promise.listeners
                BY <3>1, RecPair, Zenon DEF Due, DueN, Ids
            <3>5. /\ i \in DOMAIN cur
                  /\ cur[i] = BodyN(base, T, i)
                BY <3>1, <3>4, ListenAt, Z3 DEF cur
            <3>6. P!Project(base[i], t) = base[i]
                BY <3>4
            <3>7. base[i].promise.state /= "pending"
                BY <3>4, <3>6, GuardHeld, Zenon DEF Ids
            <3>8. a \in cur[i].promise.listeners
                <4>1. CASE Gone(i, T) = {}
                    <5>1. cur[i] = base[i]
                        BY <3>5, <4>1 DEF BodyN
                    <5>2. QED
                        BY <3>4, <5>1
                <4>2. CASE Gone(i, T) # {}
                    <5>1. cur[i] = Struck(base[i], Gone(i, T))
                        BY <3>5, <4>2 DEF BodyN
                    <5>2. a \notin Gone(i, T)
                        BY <3>1, RecPair, Zenon DEF Gone
                    <5>3. cur[i].promise.listeners
                            = base[i].promise.listeners \ Gone(i, T)
                        BY <5>1 DEF Struck
                    <5>4. a \in cur[i].promise.listeners
                        BY <3>4, <5>2, <5>3, Z3
                    <5>5. QED
                        BY <5>4
                <4>3. QED
                    BY <4>1, <4>2
            <3>9. P!Project(cur[i], t) = cur[i]
                <4>1. CASE Gone(i, T) = {}
                    BY <3>5, <3>6, <4>1, Z3 DEF BodyN
                <4>2. CASE Gone(i, T) # {}
                    <5>1. cur[i] = Struck(base[i], Gone(i, T))
                        BY <3>5, <4>2 DEF BodyN
                    <5>2. QED
                        BY <3>6, <5>1, ProjectDrop
                <4>3. QED
                    BY <4>1, <4>2
            <3>10. cur[i].promise.state = base[i].promise.state
                <4>1. CASE Gone(i, T) = {}
                    BY <3>5, <4>1, Z3 DEF BodyN
                <4>2. CASE Gone(i, T) # {}
                    <5>1. cur[i] = Struck(base[i], Gone(i, T))
                        BY <3>5, <4>2 DEF BodyN
                    <5>2. cur[i].promise.state = base[i].promise.state
                        BY <5>1 DEF Struck
                    <5>3. QED
                        BY <5>2
                <4>3. QED
                    BY <4>1, <4>2
            <3>11. Store(P!Write(cur, i, LBody(cur[i], a)),
                         Post(curb, UnblockMsg(cur, i, a, t)))
                      \in P!DueListener(cur, curb, t)
                BY <3>4, <3>5, <3>7, <3>8, <3>9, <3>10, ListenMember, Z3
            <3>12. UnblockMsg(cur, i, a, t) = UnblockMsg(base, i, a, t)
                BY <3>6, <3>9, <3>10, Z3 DEF UnblockMsg
            <3>13. Store(P!Write(cur, i, LBody(cur[i], a)),
                         Post(curb, UnblockMsg(base, i, a, t)))
                      \in D1(cur, curb, t)
                BY <3>11, <3>12, InDue1N, Z3
            <3>14. P!Write(cur, i, LBody(cur[i], a)) = ImgN(base, T \cup {x})
                BY <3>1, ListenBulk, Z3 DEF cur, i, a
            <3>15. Post(curb, UnblockMsg(base, i, a, t))
                      = BoxN(box, base, T \cup {x}, t)
                BY <3>1, BoxStepN, Z3 DEF curb, i, a
            <3>16. ReachN(base, box, t, ImgN(base, T \cup {x}),
                          BoxN(box, base, T \cup {x}, t), Cardinality(T) + 1)
                BY <3>2, <3>3, <3>13, <3>14, <3>15, ReachAppend, Z3
            <3>17. QED
                BY <2>2, <3>3, <3>16 DEF Closed
        <2>3. QED
            BY <2>1, <2>2
    <1>4. Closed(Due)
        <2>1. HIDE DEF Closed
        <2>2. QED
            BY ONLY <1>1, <1>2, <1>3, FS_Induction, Isa
    <1>5. QED
        BY <1>4 DEF Closed, Due

===============================================================================
