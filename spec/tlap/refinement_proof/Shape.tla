------------------------------ MODULE Shape ------------------------------
(* A stored origin document already has the shape a sweep is willing to
   read. Callbacks name ids of this document, so the awaiter test is the
   registered set. Listeners name addresses. An acquired task carries a
   lease and a duration, a pending task carries a retry, and a suspended
   task is still a pending promise. A ttl is a duration, so arming a lease
   at a natural time cannot land on NoTime. The two search tags have no
   handler, and the executor names at least one origin. *)
EXTENDS Concrete, SequenceTheorems, TLAPS

ASSUME TtlNat == Ttl \subseteq Nat
ASSUME RetryNat == RetryTimeout \in Nat
ASSUME Origin /= {}

Guard(obj) ==
    /\ obj.promise.listeners \subseteq Address
    /\ (obj.task.state = "acquired" =>
          /\ obj.task.leaseTimeoutAt /= NoTime
          /\ obj.task.ttl \in Ttl
          /\ obj.promise.state = "pending")
    /\ (obj.task.state = "pending" =>
          /\ obj.task.retryTimeoutAt /= NoTime
          /\ obj.promise.state = "pending")
    /\ (obj.task.state = "suspended" =>
          obj.promise.state = "pending")

DocOk(doc) ==
    /\ \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq DOMAIN doc
    /\ \A k \in DOMAIN doc : Guard(doc[k])

Home(doc, o) ==
    DOMAIN doc \subseteq { i \in Id : i.origin = o }

Placed ==
    /\ DOMAIN docs = Origin
    /\ \A o \in Origin : DocOk(docs[o]) /\ Home(docs[o], o)

LEMMA DomCtor ==
    ASSUME NEW D, NEW e(_)
    PROVE  DOMAIN [x \in D |-> e(x)] = D
PROOF
    BY ONLY Isa

LEMMA AppCtor ==
    ASSUME NEW D, NEW e(_), NEW k \in D
    PROVE  [x \in D |-> e(x)][k] = e(k)
PROOF
    BY ONLY Isa

LEMMA AtNat ==
    ASSUME NEW tm \in Nat, NEW t \in 0 .. tm
    PROVE  t \in Nat /\ t /= NoTime
PROOF
    BY ONLY Z3 DEF NoTime

LEMMA LeaseTime ==
    ASSUME NEW t \in Nat, NEW ttl \in Ttl
    PROVE  t + ttl /= NoTime
PROOF
    <1>1. ttl \in Nat
        BY TtlNat, Z3
    <1>2. QED
        BY ONLY <1>1, Z3 DEF NoTime

LEMMA RetryTime ==
    ASSUME NEW t \in Nat
    PROVE  t + RetryTimeout /= NoTime
PROOF
    BY RetryNat, Z3 DEF NoTime

LEMMA IdOrig ==
    ASSUME NEW i \in Id
    PROVE  i.origin \in Origin
PROOF
    BY ONLY Z3 DEF Id

LEMMA CreateId ==
    ASSUME NEW r \in CreateReq
    PROVE  r.id \in Id
PROOF
    BY ONLY Z3 DEF CreateReq

(* ------------------------------------------------------------------ *)

LEMMA ProjId ==
    ASSUME NEW obj, NEW t,
           obj.promise.state /= "pending" \/ ~(obj.promise.timeoutAt <= t)
    PROVE  Project(obj, t) = obj
PROOF
    BY Isa DEF Project

LEMMA ProjFields ==
    ASSUME NEW obj, NEW t,
           obj.promise.state = "pending" /\ obj.promise.timeoutAt <= t
    PROVE  /\ Project(obj, t).promise.callbacks = obj.promise.callbacks
           /\ Project(obj, t).promise.listeners = obj.promise.listeners
           /\ Project(obj, t).promise.state \in {"resolved", "rejectedTimedout"}
           /\ Project(obj, t).task.state \in {"none", "fulfilled"}
PROOF
    <1> DEFINE st == IF obj.promise.tags.timer THEN "resolved"
                     ELSE "rejectedTimedout"
    <1> DEFINE p ==
            [obj.promise EXCEPT !.state = st,
                                !.value = NoValue,
                                !.settledAt = obj.promise.timeoutAt]
    <1> DEFINE ts == IF obj.task.state = "none" THEN "none" ELSE "fulfilled"
    <1> DEFINE tk ==
            [obj.task EXCEPT !.state          = ts,
                             !.pid            = NoPid,
                             !.ttl            = NoTime,
                             !.leaseTimeoutAt = NoTime,
                             !.retryTimeoutAt = NoTime,
                             !.resumes        = {}]
    <1>1. p.callbacks = obj.promise.callbacks
          /\ p.listeners = obj.promise.listeners
          /\ p.state = st
        BY ONLY Z3 DEF p
    <1>2. tk.state = ts
        BY ONLY Z3 DEF tk
    <1>3. Project(obj, t) = [promise |-> p, task |-> tk]
        BY Isa DEF Project, st, p, ts, tk
    <1>4. st \in {"resolved", "rejectedTimedout"}
          /\ ts \in {"none", "fulfilled"}
        BY ONLY Z3 DEF st, ts
    <1>5. QED
        BY <1>1, <1>2, <1>3, <1>4, Isa

LEMMA ProjCb ==
    ASSUME NEW obj, NEW t
    PROVE  /\ Project(obj, t).promise.callbacks = obj.promise.callbacks
           /\ Project(obj, t).promise.listeners = obj.promise.listeners
PROOF
    <1>1. CASE obj.promise.state = "pending" /\ obj.promise.timeoutAt <= t
        BY ONLY <1>1, ProjFields, Z3
    <1>2. CASE obj.promise.state /= "pending" \/ ~(obj.promise.timeoutAt <= t)
        BY ONLY <1>2, ProjId, Z3
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3

LEMMA ProjAcq ==
    ASSUME NEW obj, NEW t, Project(obj, t).task.state = "acquired"
    PROVE  Project(obj, t) = obj
PROOF
    <1>1. CASE obj.promise.state = "pending" /\ obj.promise.timeoutAt <= t
        <2>1. Project(obj, t).task.state \in {"none", "fulfilled"}
            BY ONLY <1>1, ProjFields, Z3
        <2>2. QED
            BY <2>1, Isa
    <1>2. CASE obj.promise.state /= "pending" \/ ~(obj.promise.timeoutAt <= t)
        BY ONLY <1>2, ProjId, Z3
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3

LEMMA ProjGuard ==
    ASSUME NEW obj, NEW t, Guard(obj)
    PROVE  Guard(Project(obj, t))
PROOF
    <1>1. CASE obj.promise.state = "pending" /\ obj.promise.timeoutAt <= t
        <2>1. Project(obj, t).promise.listeners = obj.promise.listeners
              /\ Project(obj, t).task.state \in {"none", "fulfilled"}
            BY ONLY <1>1, ProjFields, Z3
        <2>2. obj.promise.listeners \subseteq Address
            BY Z3 DEF Guard
        <2>3. QED
            BY ONLY <2>1, <2>2, Z3 DEF Guard
    <1>2. CASE obj.promise.state /= "pending" \/ ~(obj.promise.timeoutAt <= t)
        <2>1. Project(obj, t) = obj
            BY ONLY <1>2, ProjId, Z3
        <2>2. Guard(obj)
            BY Z3 DEF Guard
        <2>3. QED
            BY ONLY <2>1, <2>2, Z3 DEF Guard
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3

(* ------------------------------------------------------------------ *)

LEMMA NewBits ==
    ASSUME NEW req, NEW t \in Nat
    PROVE  /\ New(req, t).promise.callbacks = {}
           /\ New(req, t).promise.listeners = {}
           /\ Guard(New(req, t))
PROOF
    <1>1. CASE req.timeoutAt > t /\ req.tags.targeted
        <2> DEFINE nw ==
                [ promise |->
                    [ state |-> "pending", param |-> req.param, value |-> NoValue,
                      tags |-> req.tags, timeoutAt |-> req.timeoutAt,
                      createdAt |-> t, settledAt |-> NoTime,
                      callbacks |-> {}, listeners |-> {} ],
                  task |-> [NoTask EXCEPT !.state = "pending",
                                          !.retryTimeoutAt = t] ]
        <2>1. New(req, t) = nw
            BY ONLY <1>1, Z3 DEF New, nw
        <2>2. nw.promise.callbacks = {} /\ nw.promise.listeners = {}
              /\ nw.promise.state = "pending"
            BY ONLY Z3 DEF nw
        <2>3. nw.task.state = "pending" /\ nw.task.retryTimeoutAt = t
            <3> DEFINE t1 == [NoTask EXCEPT !.state = "pending"]
            <3> DEFINE t2 == [t1 EXCEPT !.retryTimeoutAt = t]
            <3>1. t1.state = "pending"
                BY ONLY Z3 DEF t1, NoTask
            <3>2. t2.state = t1.state /\ t2.retryTimeoutAt = t
                BY ONLY Z3 DEF t2
            <3>3. nw.task = t2
                BY Zenon DEF nw, t1, t2, NoTask
            <3>4. nw.task.state = t2.state
                  /\ nw.task.retryTimeoutAt = t2.retryTimeoutAt
                BY ONLY <3>3, Isa
            <3>5. QED
                BY ONLY <3>1, <3>2, <3>4, Z3
        <2>4. t /= NoTime
            BY ONLY Z3 DEF NoTime
        <2>5. QED
            BY ONLY <2>1, <2>2, <2>3, <2>4, Z3 DEF Guard
    <1>2. CASE req.timeoutAt > t /\ ~req.tags.targeted
        <2> DEFINE nw ==
                [ promise |->
                    [ state |-> "pending", param |-> req.param, value |-> NoValue,
                      tags |-> req.tags, timeoutAt |-> req.timeoutAt,
                      createdAt |-> t, settledAt |-> NoTime,
                      callbacks |-> {}, listeners |-> {} ],
                  task |-> NoTask ]
        <2>1. New(req, t) = nw
            BY ONLY <1>2, Z3 DEF New, nw
        <2>2. nw.promise.callbacks = {} /\ nw.promise.listeners = {}
              /\ nw.task.state = "none"
            BY ONLY Z3 DEF nw, NoTask
        <2>3. QED
            BY ONLY <2>1, <2>2, Z3 DEF Guard
    <1>3. CASE ~(req.timeoutAt > t) /\ req.tags.targeted
        <2> DEFINE nw ==
                [ promise |->
                    [ state |-> IF req.tags.timer THEN "resolved"
                                ELSE "rejectedTimedout",
                      param |-> req.param, value |-> NoValue, tags |-> req.tags,
                      timeoutAt |-> req.timeoutAt, createdAt |-> req.timeoutAt,
                      settledAt |-> req.timeoutAt,
                      callbacks |-> {}, listeners |-> {} ],
                  task |-> [NoTask EXCEPT !.state = "fulfilled"] ]
        <2>1. New(req, t) = nw
            BY ONLY <1>3, Z3 DEF New, nw
        <2>2. nw.promise.callbacks = {} /\ nw.promise.listeners = {}
              /\ nw.task.state = "fulfilled"
            BY ONLY Z3 DEF nw, NoTask
        <2>3. QED
            BY ONLY <2>1, <2>2, Z3 DEF Guard
    <1>4. CASE ~(req.timeoutAt > t) /\ ~req.tags.targeted
        <2> DEFINE nw ==
                [ promise |->
                    [ state |-> IF req.tags.timer THEN "resolved"
                                ELSE "rejectedTimedout",
                      param |-> req.param, value |-> NoValue, tags |-> req.tags,
                      timeoutAt |-> req.timeoutAt, createdAt |-> req.timeoutAt,
                      settledAt |-> req.timeoutAt,
                      callbacks |-> {}, listeners |-> {} ],
                  task |-> NoTask ]
        <2>1. New(req, t) = nw
            BY ONLY <1>4, Z3 DEF New, nw
        <2>2. nw.promise.callbacks = {} /\ nw.promise.listeners = {}
              /\ nw.task.state = "none"
            BY ONLY Z3 DEF nw, NoTask
        <2>3. QED
            BY ONLY <2>1, <2>2, Z3 DEF Guard
    <1>5. QED
        BY ONLY <1>1, <1>2, <1>3, <1>4, Z3

(* ------------------------------------------------------------------ *)

LEMMA WriteDom ==
    ASSUME NEW doc, NEW id, NEW obj
    PROVE  DOMAIN Write(doc, id, obj) = (DOMAIN doc) \cup {id}
PROOF
    BY DomCtor, Isa DEF Write

LEMMA WriteAt ==
    ASSUME NEW doc, NEW id, NEW obj, NEW k \in (DOMAIN doc) \cup {id}
    PROVE  Write(doc, id, obj)[k] = IF k = id THEN obj ELSE doc[k]
PROOF
    <1> DEFINE D == (DOMAIN doc) \cup {id}
    <1> DEFINE e(x) == IF x = id THEN obj ELSE doc[x]
    <1>1. Write(doc, id, obj) = [x \in D |-> e(x)]
        BY ONLY DEF Write, D, e
    <1>2. [x \in D |-> e(x)][k] = e(k)
        BY ONLY AppCtor DEF D
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3 DEF e

LEMMA WriteOk ==
    ASSUME NEW doc, NEW id, NEW obj,
           DocOk(doc), Guard(obj),
           obj.promise.callbacks \subseteq (DOMAIN doc) \cup {id}
    PROVE  DocOk(Write(doc, id, obj))
PROOF
    <1> DEFINE w == Write(doc, id, obj)
    <1>1. DOMAIN w = (DOMAIN doc) \cup {id}
        BY ONLY WriteDom DEF w
    <1>2. ASSUME NEW k \in DOMAIN w
          PROVE  w[k].promise.callbacks \subseteq DOMAIN w /\ Guard(w[k])
        <2>1. w[k] = IF k = id THEN obj ELSE doc[k]
            BY ONLY <1>1, WriteAt, Z3 DEF w
        <2>2. CASE k = id
            BY <1>1, <2>1, <2>2, Isa
        <2>3. CASE k /= id
            <3>1. k \in DOMAIN doc
                BY ONLY <1>1, <2>3, Z3
            <3>2. doc[k].promise.callbacks \subseteq DOMAIN doc /\ Guard(doc[k])
                BY <3>1, Isa DEF DocOk
            <3>3. DOMAIN doc \subseteq DOMAIN w
                BY ONLY <1>1, Z3
            <3>4. QED
                BY ONLY <2>1, <2>3, <3>2, <3>3, Z3
        <2>4. QED
            BY ONLY <2>2, <2>3, Z3
    <1>3. QED
        BY ONLY <1>2, Z3 DEF DocOk, w

LEMMA WriteHome ==
    ASSUME NEW doc, NEW o, NEW id, NEW obj,
           Home(doc, o), id \in Id, id.origin = o
    PROVE  Home(Write(doc, id, obj), o)
PROOF
    <1>1. DOMAIN Write(doc, id, obj) = (DOMAIN doc) \cup {id}
        BY ONLY WriteDom, Z3
    <1>2. id \in { i \in Id : i.origin = o }
        BY Isa
    <1>3. (DOMAIN doc) \cup {id} \subseteq { i \in Id : i.origin = o }
        BY <1>2, Isa DEF Home
    <1>4. QED
        BY ONLY <1>1, <1>3, Z3 DEF Home

LEMMA SameHome ==
    ASSUME NEW doc, NEW doc2, NEW o,
           Home(doc, o), DOMAIN doc2 = DOMAIN doc
    PROVE  Home(doc2, o)
PROOF
    BY Isa DEF Home

LEMMA SkipBoth ==
    ASSUME NEW doc, NEW o, DocOk(doc), Home(doc, o)
    PROVE  DocOk(Skip(doc).doc) /\ Home(Skip(doc).doc, o)
PROOF
    BY Isa DEF Skip

(* ------------------------------------------------------------------ *)

AcqOf(obj, ttl, pid, at) ==
    [obj EXCEPT !.task.state          = "acquired",
                !.task.version        = @ + 1,
                !.task.ttl            = ttl,
                !.task.pid            = pid,
                !.task.leaseTimeoutAt = at,
                !.task.retryTimeoutAt = NoTime,
                !.task.resumes        = {}]

PendOf(obj, at) ==
    [obj EXCEPT !.task.state          = "pending",
                !.task.pid            = NoPid,
                !.task.ttl            = NoTime,
                !.task.leaseTimeoutAt = NoTime,
                !.task.retryTimeoutAt = at]

HaltOf(obj) ==
    [obj EXCEPT !.task.state          = "halted",
                !.task.pid            = NoPid,
                !.task.ttl            = NoTime,
                !.task.leaseTimeoutAt = NoTime,
                !.task.retryTimeoutAt = NoTime]

SusOf(obj) ==
    [obj EXCEPT !.task.state          = "suspended",
                !.task.pid            = NoPid,
                !.task.ttl            = NoTime,
                !.task.leaseTimeoutAt = NoTime,
                !.task.retryTimeoutAt = NoTime,
                !.task.resumes        = {}]

WithCb(obj, c) ==
    [obj EXCEPT !.promise.callbacks = c]

WithLs(obj, ls) ==
    [obj EXCEPT !.promise.listeners = ls]

LEMMA AcqFields ==
    ASSUME NEW obj, NEW ttl, NEW pid, NEW at
    PROVE  /\ AcqOf(obj, ttl, pid, at).task.state = "acquired"
           /\ AcqOf(obj, ttl, pid, at).task.ttl = ttl
           /\ AcqOf(obj, ttl, pid, at).task.leaseTimeoutAt = at
           /\ AcqOf(obj, ttl, pid, at).promise = obj.promise
PROOF
    <1> DEFINE k1 == [obj.task EXCEPT !.state = "acquired"]
    <1> DEFINE k2 == [k1 EXCEPT !.version = k1.version + 1]
    <1> DEFINE k3 == [k2 EXCEPT !.ttl = ttl]
    <1> DEFINE k4 == [k3 EXCEPT !.pid = pid]
    <1> DEFINE k5 == [k4 EXCEPT !.leaseTimeoutAt = at]
    <1> DEFINE k6 == [k5 EXCEPT !.retryTimeoutAt = NoTime]
    <1> DEFINE k7 == [k6 EXCEPT !.resumes = {}]
    <1> DEFINE nw == [obj EXCEPT !.task = k7]
    <1>1. k1.state = "acquired"
        BY ONLY Z3 DEF k1
    <1>2. k2.state = k1.state /\ k2.ttl = k1.ttl
        BY ONLY Z3 DEF k2
    <1>3. k3.state = k2.state /\ k3.ttl = ttl
        BY ONLY Z3 DEF k3
    <1>4. k4.state = k3.state /\ k4.ttl = k3.ttl
        BY ONLY Z3 DEF k4
    <1>5. k5.state = k4.state /\ k5.ttl = k4.ttl
          /\ k5.leaseTimeoutAt = at
        BY ONLY Z3 DEF k5
    <1>6. k6.state = k5.state /\ k6.ttl = k5.ttl
          /\ k6.leaseTimeoutAt = k5.leaseTimeoutAt
        BY ONLY Z3 DEF k6
    <1>7. k7.state = k6.state /\ k7.ttl = k6.ttl
          /\ k7.leaseTimeoutAt = k6.leaseTimeoutAt
        BY ONLY Z3 DEF k7
    <1>8. nw.task = k7 /\ nw.promise = obj.promise
        BY ONLY Z3 DEF nw
    <1>9. AcqOf(obj, ttl, pid, at) = nw
        BY Zenon DEF AcqOf, k1, k2, k3, k4, k5, k6, k7, nw
    <1>10. k7.state = "acquired" /\ k7.ttl = ttl
           /\ k7.leaseTimeoutAt = at
        BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, Z3
    <1>11. nw.task.state = k7.state /\ nw.task.ttl = k7.ttl
           /\ nw.task.leaseTimeoutAt = k7.leaseTimeoutAt
           /\ nw.promise = obj.promise
        BY ONLY <1>8, Isa
    <1>12. nw.task.state = "acquired" /\ nw.task.ttl = ttl
           /\ nw.task.leaseTimeoutAt = at
        BY ONLY <1>10, <1>11, Z3
    <1>13. QED
        BY ONLY <1>9, <1>12, Z3

LEMMA AcqGuard ==
    ASSUME NEW obj, NEW ttl \in Ttl, NEW pid, NEW t \in Nat,
           obj.promise.state = "pending",
           obj.promise.listeners \subseteq Address
    PROVE  Guard(AcqOf(obj, ttl, pid, t + ttl))
           /\ AcqOf(obj, ttl, pid, t + ttl).promise.callbacks
                = obj.promise.callbacks
PROOF
    <1> DEFINE nw == AcqOf(obj, ttl, pid, t + ttl)
    <1>1. nw.task.state = "acquired" /\ nw.task.ttl = ttl
          /\ nw.task.leaseTimeoutAt = t + ttl /\ nw.promise = obj.promise
        BY ONLY AcqFields DEF nw
    <1>2. t + ttl /= NoTime
        BY ONLY LeaseTime, Z3
    <1>3. QED
        BY <1>1, <1>2, Isa DEF Guard, nw

LEMMA PendFields ==
    ASSUME NEW obj, NEW at
    PROVE  /\ PendOf(obj, at).promise = obj.promise
           /\ PendOf(obj, at).task.state = "pending"
           /\ PendOf(obj, at).task.retryTimeoutAt = at
PROOF
    <1> DEFINE k1 == [obj.task EXCEPT !.state = "pending"]
    <1> DEFINE k2 == [k1 EXCEPT !.pid = NoPid]
    <1> DEFINE k3 == [k2 EXCEPT !.ttl = NoTime]
    <1> DEFINE k4 == [k3 EXCEPT !.leaseTimeoutAt = NoTime]
    <1> DEFINE k5 == [k4 EXCEPT !.retryTimeoutAt = at]
    <1> DEFINE nw == [obj EXCEPT !.task = k5]
    <1>1. k1.state = "pending"
        BY ONLY Z3 DEF k1
    <1>2. k2.state = k1.state
        BY ONLY Z3 DEF k2
    <1>3. k3.state = k2.state
        BY ONLY Z3 DEF k3
    <1>4. k4.state = k3.state
        BY ONLY Z3 DEF k4
    <1>5. k5.state = k4.state /\ k5.retryTimeoutAt = at
        BY ONLY Z3 DEF k5
    <1>6. nw.task = k5 /\ nw.promise = obj.promise
        BY ONLY Z3 DEF nw
    <1>7. PendOf(obj, at) = nw
        BY Zenon DEF PendOf, k1, k2, k3, k4, k5, nw
    <1>8. k5.state = "pending"
        BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5, Z3
    <1>9. nw.task.state = k5.state /\ nw.task.retryTimeoutAt = k5.retryTimeoutAt
          /\ nw.promise = obj.promise
        BY ONLY <1>6, Isa
    <1>10. QED
        BY ONLY <1>5, <1>7, <1>8, <1>9, Z3

LEMMA PendGuard ==
    ASSUME NEW obj, NEW t \in Nat,
           obj.promise.state = "pending",
           obj.promise.listeners \subseteq Address,
           obj.promise.callbacks \subseteq obj.promise.callbacks
    PROVE  Guard(PendOf(obj, t))
           /\ PendOf(obj, t).promise.callbacks = obj.promise.callbacks
PROOF
    <1>1. PendOf(obj, t).promise = obj.promise
          /\ PendOf(obj, t).task.state = "pending"
          /\ PendOf(obj, t).task.retryTimeoutAt = t
        BY ONLY PendFields, Z3
    <1>2. t /= NoTime
        BY ONLY Z3 DEF NoTime
    <1>3. QED
        BY <1>1, <1>2, Isa DEF Guard

LEMMA HaltFields ==
    ASSUME NEW obj
    PROVE  HaltOf(obj).promise = obj.promise
           /\ HaltOf(obj).task.state = "halted"
PROOF
    <1> DEFINE k1 == [obj.task EXCEPT !.state = "halted"]
    <1> DEFINE k2 == [k1 EXCEPT !.pid = NoPid]
    <1> DEFINE k3 == [k2 EXCEPT !.ttl = NoTime]
    <1> DEFINE k4 == [k3 EXCEPT !.leaseTimeoutAt = NoTime]
    <1> DEFINE k5 == [k4 EXCEPT !.retryTimeoutAt = NoTime]
    <1> DEFINE nw == [obj EXCEPT !.task = k5]
    <1>1. k1.state = "halted"
        BY ONLY Z3 DEF k1
    <1>2. k2.state = k1.state
        BY ONLY Z3 DEF k2
    <1>3. k3.state = k2.state
        BY ONLY Z3 DEF k3
    <1>4. k4.state = k3.state
        BY ONLY Z3 DEF k4
    <1>5. k5.state = k4.state
        BY ONLY Z3 DEF k5
    <1>6. nw.task = k5 /\ nw.promise = obj.promise
        BY ONLY Z3 DEF nw
    <1>7. HaltOf(obj) = nw
        BY Zenon DEF HaltOf, k1, k2, k3, k4, k5, nw
    <1>8. k5.state = "halted"
        BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5, Z3
    <1>9. nw.task.state = k5.state /\ nw.promise = obj.promise
        BY ONLY <1>6, Isa
    <1>10. QED
        BY ONLY <1>7, <1>8, <1>9, Z3

LEMMA SusFields ==
    ASSUME NEW obj
    PROVE  SusOf(obj).promise = obj.promise
           /\ SusOf(obj).task.state = "suspended"
PROOF
    <1> DEFINE k1 == [obj.task EXCEPT !.state = "suspended"]
    <1> DEFINE k2 == [k1 EXCEPT !.pid = NoPid]
    <1> DEFINE k3 == [k2 EXCEPT !.ttl = NoTime]
    <1> DEFINE k4 == [k3 EXCEPT !.leaseTimeoutAt = NoTime]
    <1> DEFINE k5 == [k4 EXCEPT !.retryTimeoutAt = NoTime]
    <1> DEFINE k6 == [k5 EXCEPT !.resumes = {}]
    <1> DEFINE nw == [obj EXCEPT !.task = k6]
    <1>1. k1.state = "suspended"
        BY ONLY Z3 DEF k1
    <1>2. k2.state = k1.state
        BY ONLY Z3 DEF k2
    <1>3. k3.state = k2.state
        BY ONLY Z3 DEF k3
    <1>4. k4.state = k3.state
        BY ONLY Z3 DEF k4
    <1>5. k5.state = k4.state
        BY ONLY Z3 DEF k5
    <1>6. k6.state = k5.state
        BY ONLY Z3 DEF k6
    <1>7. nw.task = k6 /\ nw.promise = obj.promise
        BY ONLY Z3 DEF nw
    <1>8. SusOf(obj) = nw
        BY Zenon DEF SusOf, k1, k2, k3, k4, k5, k6, nw
    <1>9. k6.state = "suspended"
        BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, Z3
    <1>10. nw.task.state = k6.state /\ nw.promise = obj.promise
        BY ONLY <1>7, Isa
    <1>11. QED
        BY ONLY <1>8, <1>9, <1>10, Z3

LEMMA CbFields ==
    ASSUME NEW obj, NEW c
    PROVE  /\ WithCb(obj, c).promise.callbacks = c
           /\ WithCb(obj, c).promise.listeners = obj.promise.listeners
           /\ WithCb(obj, c).promise.state = obj.promise.state
           /\ WithCb(obj, c).task = obj.task
PROOF
    <1> DEFINE p == [obj.promise EXCEPT !.callbacks = c]
    <1> DEFINE nw == [obj EXCEPT !.promise = p]
    <1>1. p.callbacks = c
          /\ p.listeners = obj.promise.listeners
          /\ p.state = obj.promise.state
        BY ONLY Z3 DEF p
    <1>2. nw.promise = p /\ nw.task = obj.task
        BY ONLY Z3 DEF nw
    <1>3. WithCb(obj, c) = nw
        BY Zenon DEF WithCb, p, nw
    <1>4. nw.promise.callbacks = p.callbacks
          /\ nw.promise.listeners = p.listeners
          /\ nw.promise.state = p.state
        BY ONLY <1>2, Isa
    <1>5. nw.promise.callbacks = c
          /\ nw.promise.listeners = obj.promise.listeners
          /\ nw.promise.state = obj.promise.state
          /\ nw.task = obj.task
        BY ONLY <1>1, <1>2, <1>4, Z3
    <1>6. QED
        BY ONLY <1>3, <1>5, Z3

LEMMA LsFields ==
    ASSUME NEW obj, NEW ls
    PROVE  /\ WithLs(obj, ls).promise.listeners = ls
           /\ WithLs(obj, ls).promise.callbacks = obj.promise.callbacks
           /\ WithLs(obj, ls).promise.state = obj.promise.state
           /\ WithLs(obj, ls).task = obj.task
PROOF
    <1> DEFINE p == [obj.promise EXCEPT !.listeners = ls]
    <1> DEFINE nw == [obj EXCEPT !.promise = p]
    <1>1. p.listeners = ls
          /\ p.callbacks = obj.promise.callbacks
          /\ p.state = obj.promise.state
        BY ONLY Z3 DEF p
    <1>2. nw.promise = p /\ nw.task = obj.task
        BY ONLY Z3 DEF nw
    <1>3. WithLs(obj, ls) = nw
        BY Zenon DEF WithLs, p, nw
    <1>4. nw.promise.listeners = p.listeners
          /\ nw.promise.callbacks = p.callbacks
          /\ nw.promise.state = p.state
        BY ONLY <1>2, Isa
    <1>5. nw.promise.listeners = ls
          /\ nw.promise.callbacks = obj.promise.callbacks
          /\ nw.promise.state = obj.promise.state
          /\ nw.task = obj.task
        BY ONLY <1>1, <1>2, <1>4, Z3
    <1>6. QED
        BY ONLY <1>3, <1>5, Z3

LEMMA CbGuard ==
    ASSUME NEW obj, NEW a, Guard(obj),
           obj.promise.callbacks \cup {a} \subseteq obj.promise.callbacks \cup {a}
    PROVE  Guard(WithCb(obj, obj.promise.callbacks \cup {a}))
PROOF
    <1> DEFINE nw == WithCb(obj, obj.promise.callbacks \cup {a})
    <1>1. nw.promise.listeners = obj.promise.listeners
          /\ nw.promise.state = obj.promise.state
          /\ nw.task = obj.task
        BY ONLY CbFields DEF nw
    <1>2. QED
        BY <1>1, Isa DEF Guard, nw

LEMMA LsGuard ==
    ASSUME NEW obj, NEW a \in Address, Guard(obj)
    PROVE  Guard(WithLs(obj, obj.promise.listeners \cup {a}))
           /\ WithLs(obj, obj.promise.listeners \cup {a}).promise.callbacks
                = obj.promise.callbacks
PROOF
    <1> DEFINE nw == WithLs(obj, obj.promise.listeners \cup {a})
    <1>1. nw.promise.listeners = obj.promise.listeners \cup {a}
          /\ nw.promise.callbacks = obj.promise.callbacks
          /\ nw.promise.state = obj.promise.state
          /\ nw.task = obj.task
        BY ONLY LsFields DEF nw
    <1>2. obj.promise.listeners \subseteq Address
        BY Isa DEF Guard
    <1>3. QED
        BY <1>1, <1>2, Isa DEF Guard, nw

(* ------------------------------------------------------------------ *)

LEMMA CreateOk ==
    ASSUME NEW req, NEW doc, NEW t \in Nat, NEW o,
           DocOk(doc), Home(doc, o),
           req.id \in Id, req.id.origin = o
    PROVE  DocOk(HandlePromiseCreate(req, doc, t).doc)
           /\ Home(HandlePromiseCreate(req, doc, t).doc, o)
PROOF
    <1>1. CASE req.id \in DOMAIN doc
        <2>1. HandlePromiseCreate(req, doc, t) = Skip(doc)
            BY ONLY <1>1, Z3 DEF HandlePromiseCreate
        <2>2. QED
            BY <2>1, SkipBoth, Isa
    <1>2. CASE req.id \notin DOMAIN doc
        <2> DEFINE nw == New(req, t)
        <2>1. nw.promise.callbacks = {} /\ Guard(nw)
            BY ONLY NewBits DEF nw
        <2>2. HandlePromiseCreate(req, doc, t).doc = Write(doc, req.id, nw)
            BY ONLY <1>2, Z3 DEF HandlePromiseCreate, nw
        <2>3. {} \subseteq (DOMAIN doc) \cup {req.id}
            BY ONLY Z3
        <2>4. DocOk(Write(doc, req.id, nw))
            BY <2>1, <2>3, WriteOk, Isa DEF nw
        <2>5. Home(Write(doc, req.id, nw), o)
            BY WriteHome, Isa DEF nw
        <2>6. QED
            BY ONLY <2>2, <2>4, <2>5, Z3
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3

Settled(old, st, val, tm) ==
    [ promise |-> [old.promise EXCEPT !.state = st,
                                       !.value = val,
                                       !.settledAt = tm],
      task    |-> [old.task EXCEPT !.state = IF @ = "none" THEN "none"
                                              ELSE "fulfilled",
                                   !.pid = NoPid,
                                   !.ttl = NoTime,
                                   !.leaseTimeoutAt = NoTime,
                                   !.retryTimeoutAt = NoTime,
                                   !.resumes = {}] ]

LEMMA SettleBody ==
    ASSUME NEW old, NEW st, NEW val, NEW tm, Guard(old)
    PROVE  Guard(Settled(old, st, val, tm))
           /\ Settled(old, st, val, tm).promise.callbacks = old.promise.callbacks
           /\ Settled(old, st, val, tm).promise.listeners = old.promise.listeners
PROOF
    <1> DEFINE ts == IF old.task.state = "none" THEN "none" ELSE "fulfilled"
    <1> DEFINE p1 == [old.promise EXCEPT !.state = st]
    <1> DEFINE p2 == [p1 EXCEPT !.value = val]
    <1> DEFINE p3 == [p2 EXCEPT !.settledAt = tm]
    <1> DEFINE k1 == [old.task EXCEPT !.state = ts]
    <1> DEFINE k2 == [k1 EXCEPT !.pid = NoPid]
    <1> DEFINE k3 == [k2 EXCEPT !.ttl = NoTime]
    <1> DEFINE k4 == [k3 EXCEPT !.leaseTimeoutAt = NoTime]
    <1> DEFINE k5 == [k4 EXCEPT !.retryTimeoutAt = NoTime]
    <1> DEFINE k6 == [k5 EXCEPT !.resumes = {}]
    <1> DEFINE nw == [promise |-> p3, task |-> k6]
    <1>1. p1.callbacks = old.promise.callbacks
          /\ p1.listeners = old.promise.listeners
          /\ p1.state = st
        BY ONLY Z3 DEF p1
    <1>2. p2.callbacks = p1.callbacks /\ p2.listeners = p1.listeners
          /\ p2.state = p1.state
        BY ONLY Z3 DEF p2
    <1>3. p3.callbacks = p2.callbacks /\ p3.listeners = p2.listeners
          /\ p3.state = p2.state
        BY ONLY Z3 DEF p3
    <1>4. k1.state = ts
        BY ONLY Z3 DEF k1, ts
    <1>5. k2.state = k1.state
        BY ONLY Z3 DEF k2
    <1>6. k3.state = k2.state
        BY ONLY Z3 DEF k3
    <1>7. k4.state = k3.state
        BY ONLY Z3 DEF k4
    <1>8. k5.state = k4.state
        BY ONLY Z3 DEF k5
    <1>9. k6.state = k5.state
        BY ONLY Z3 DEF k6
    <1>10. ts \in {"none", "fulfilled"}
        BY ONLY Z3 DEF ts
    <1>11. nw.promise = p3 /\ nw.task = k6
        BY ONLY Z3 DEF nw
    <1>12. p3.callbacks = old.promise.callbacks
           /\ p3.listeners = old.promise.listeners
        BY ONLY <1>1, <1>2, <1>3, Z3
    <1>13. k6.state = ts
        BY ONLY <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, Z3
    <1>14. nw.promise.callbacks = p3.callbacks
           /\ nw.promise.listeners = p3.listeners
           /\ nw.task.state = k6.state
        BY ONLY <1>11, Isa
    <1>15. Settled(old, st, val, tm) = nw
        BY Zenon DEF Settled, ts, p1, p2, p3, k1, k2, k3, k4, k5, k6, nw
    <1>16. old.promise.listeners \subseteq Address
        BY Z3 DEF Guard
    <1>17. Guard(nw)
        BY ONLY <1>10, <1>12, <1>13, <1>14, <1>16, Z3 DEF Guard
    <1>18. QED
        BY ONLY <1>12, <1>14, <1>15, <1>17, Z3

LEMMA SettleOk ==
    ASSUME NEW req, NEW doc, NEW t, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(HandlePromiseSettle(req, doc, t).doc)
           /\ Home(HandlePromiseSettle(req, doc, t).doc, o)
PROOF
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. HandlePromiseSettle(req, doc, t) = Skip(doc)
            BY ONLY <1>1, Z3 DEF HandlePromiseSettle
        <2>2. QED
            BY <2>1, SkipBoth, Isa
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2> DEFINE nw == Settled(old, req.state, req.value, t)
        <2>1. CASE old.promise.state /= "pending"
            <3>1. HandlePromiseSettle(req, doc, t) = Skip(doc)
                BY ONLY <1>2, <2>1, Z3 DEF HandlePromiseSettle, old
            <3>2. QED
                BY <3>1, SkipBoth, Isa
        <2>2. CASE old.promise.state = "pending"
            <3>1. Guard(old)
                BY <1>2, ProjGuard, Isa DEF DocOk, old
            <3>2. Guard(nw)
                  /\ nw.promise.callbacks = old.promise.callbacks
                  /\ nw.promise.listeners = old.promise.listeners
                BY ONLY <3>1, SettleBody, Z3 DEF nw
            <3>3. old.promise.callbacks = doc[req.id].promise.callbacks
                BY ONLY ProjCb DEF old
            <3>4. doc[req.id].promise.callbacks \subseteq DOMAIN doc
                BY <1>2, Isa DEF DocOk
            <3>5. HandlePromiseSettle(req, doc, t).doc = Write(doc, req.id, nw)
                <4>1. HandlePromiseSettle(req, doc, t) =
                        IF req.id \notin DOMAIN doc THEN Skip(doc)
                        ELSE LET old == Project(doc[req.id], t)
                                 new == Settled(old, req.state, req.value, t)
                             IN IF old.promise.state /= "pending" THEN Skip(doc)
                                ELSE [ doc |-> Write(doc, req.id, new),
                                       puts |-> << >>,
                                       dels |-> << [at |-> old.promise.timeoutAt,
                                                    id |-> req.id,
                                                    kind |-> "promise"] >>
                                              \o (IF old.task.state = "acquired" THEN
                                                      << [at |-> old.task.leaseTimeoutAt,
                                                          id |-> req.id,
                                                          kind |-> "lease"] >>
                                                  ELSE << >>)
                                              \o (IF old.task.state = "pending" THEN
                                                      << [at |-> old.task.retryTimeoutAt,
                                                          id |-> req.id,
                                                          kind |-> "retry"] >>
                                                  ELSE << >>),
                                       sends |-> << >> ]
                    BY ONLY DEF HandlePromiseSettle, Settled
                <4>2. QED
                    BY ONLY <1>2, <2>2, <4>1, Z3 DEF old, nw
            <3>6. DOMAIN Write(doc, req.id, nw) = DOMAIN doc
                <4>1. DOMAIN Write(doc, req.id, nw) = (DOMAIN doc) \cup {req.id}
                    BY WriteDom, Isa
                <4>2. QED
                    BY ONLY <1>2, <4>1, Z3
            <3>7. nw.promise.callbacks \subseteq DOMAIN doc
                BY ONLY <3>2, <3>3, <3>4, Z3
            <3>8. DocOk(Write(doc, req.id, nw))
                <4>1. nw.promise.callbacks \subseteq (DOMAIN doc) \cup {req.id}
                    BY ONLY <3>7, Z3
                <4>2. DocOk(doc) /\ Guard(nw)
                    BY <3>2, Z3 DEF DocOk
                <4>3. QED
                    BY ONLY <4>1, <4>2, WriteOk, Z3
            <3>9. Home(Write(doc, req.id, nw), o)
                BY <3>6, SameHome, Isa
            <3>10. QED
                BY ONLY <3>5, <3>8, <3>9, Z3
        <2>3. QED
            BY ONLY <2>1, <2>2, Z3
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3

LEMMA RegCbOk ==
    ASSUME NEW req, NEW doc, NEW t, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(HandlePromiseRegisterCallback(req, doc, t).doc)
           /\ Home(HandlePromiseRegisterCallback(req, doc, t).doc, o)
PROOF
    <1> DEFINE bad ==
            \/ req.awaited \notin DOMAIN doc
            \/ req.awaiter \notin DOMAIN doc
    <1>1. CASE bad
        <2>1. HandlePromiseRegisterCallback(req, doc, t) = Skip(doc)
            BY ONLY <1>1, Z3 DEF HandlePromiseRegisterCallback, bad
        <2>2. QED
            BY <2>1, SkipBoth, Isa
    <1>2. CASE ~bad
        <2> DEFINE awaited == Project(doc[req.awaited], t)
        <2> DEFINE awaiter == Project(doc[req.awaiter], t)
        <2> DEFINE nw ==
                WithCb(awaited, awaited.promise.callbacks \cup {req.awaiter})
        <2>1. req.awaited \in DOMAIN doc /\ req.awaiter \in DOMAIN doc
            BY ONLY <1>2, Z3 DEF bad
        <2>2. awaited.promise.callbacks = doc[req.awaited].promise.callbacks
              /\ awaited.promise.listeners = doc[req.awaited].promise.listeners
            BY ONLY ProjCb DEF awaited
        <2>3. Guard(doc[req.awaited])
              /\ doc[req.awaited].promise.callbacks \subseteq DOMAIN doc
            BY <2>1, Isa DEF DocOk
        <2>4. Guard(awaited)
            BY <2>1, ProjGuard, Isa DEF DocOk, awaited
        <2>5. Guard(nw)
              /\ nw.promise.callbacks
                   = awaited.promise.callbacks \cup {req.awaiter}
            <3>1. nw.promise.listeners = awaited.promise.listeners
                  /\ nw.promise.state = awaited.promise.state
                  /\ nw.task = awaited.task
                  /\ nw.promise.callbacks
                       = awaited.promise.callbacks \cup {req.awaiter}
                BY ONLY CbFields DEF nw
            <3>2. QED
                BY <2>4, <3>1, Isa DEF Guard, nw
        <2>6. nw.promise.callbacks \subseteq DOMAIN doc
            BY ONLY <2>1, <2>2, <2>3, <2>5, Z3
        <2>7. CASE \/ ~awaiter.promise.tags.targeted
                   \/ ~IsExternal(awaited.promise)
                   \/ awaited.promise.state /= "pending"
                   \/ awaiter.promise.state /= "pending"
            <3>1. HandlePromiseRegisterCallback(req, doc, t) = Skip(doc)
                BY ONLY <1>2, <2>1, <2>7, Z3
                   DEF HandlePromiseRegisterCallback, awaited, awaiter, bad
            <3>2. QED
                BY <3>1, SkipBoth, Isa
        <2>8. CASE /\ awaiter.promise.tags.targeted
                   /\ IsExternal(awaited.promise)
                   /\ awaited.promise.state = "pending"
                   /\ awaiter.promise.state = "pending"
            <3> DEFINE built ==
                    [awaited EXCEPT !.promise.callbacks =
                         @ \cup {req.awaiter}]
            <3>1. built = nw
                BY ONLY Z3 DEF built, nw, WithCb
            <3>2. HandlePromiseRegisterCallback(req, doc, t).doc
                    = Write(doc, req.awaited, built)
                BY ONLY <1>2, <2>1, <2>8, Z3
                   DEF HandlePromiseRegisterCallback, awaited, awaiter, built, bad
            <3>3. DOMAIN Write(doc, req.awaited, nw) = DOMAIN doc
                <4>1. DOMAIN Write(doc, req.awaited, nw)
                        = (DOMAIN doc) \cup {req.awaited}
                    BY WriteDom, Isa
                <4>2. QED
                    BY ONLY <2>1, <4>1, Z3
            <3>4. DocOk(Write(doc, req.awaited, nw))
                <4>1. nw.promise.callbacks \subseteq (DOMAIN doc) \cup {req.awaited}
                    BY ONLY <2>6, Z3
                <4>2. DocOk(doc) /\ Guard(nw)
                    BY <2>5, Z3 DEF DocOk
                <4>3. QED
                    BY ONLY <4>1, <4>2, WriteOk, Z3
            <3>5. Home(Write(doc, req.awaited, nw), o)
                BY <3>3, SameHome, Isa
            <3>6. QED
                BY ONLY <3>1, <3>2, <3>4, <3>5, Z3
        <2>9. QED
            BY ONLY <2>7, <2>8, Z3
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3

LEMMA RegLsOk ==
    ASSUME NEW ev, NEW doc, NEW t, NEW o,
           DocOk(doc), Home(doc, o),
           ev.address \in Address
    PROVE  DocOk(HandlePromiseRegisterListener(ev, doc, t).doc)
           /\ Home(HandlePromiseRegisterListener(ev, doc, t).doc, o)
PROOF
    <1>1. CASE ev.awaited \notin DOMAIN doc
        <2>1. HandlePromiseRegisterListener(ev, doc, t) = Skip(doc)
            BY ONLY <1>1, Z3 DEF HandlePromiseRegisterListener
        <2>2. QED
            BY <2>1, SkipBoth, Isa
    <1>2. CASE ev.awaited \in DOMAIN doc
        <2> DEFINE old == Project(doc[ev.awaited], t)
        <2> DEFINE nw == WithLs(old, old.promise.listeners \cup {ev.address})
        <2>1. Guard(old)
            BY <1>2, ProjGuard, Isa DEF DocOk, old
        <2>2. Guard(nw) /\ nw.promise.callbacks = old.promise.callbacks
            BY <2>1, LsGuard, Isa DEF nw
        <2>3. old.promise.callbacks = doc[ev.awaited].promise.callbacks
            BY ONLY ProjCb DEF old
        <2>4. doc[ev.awaited].promise.callbacks \subseteq DOMAIN doc
            BY <1>2, Isa DEF DocOk
        <2>5. CASE ~IsExternal(old.promise) \/ old.promise.state /= "pending"
            <3>1. HandlePromiseRegisterListener(ev, doc, t) = Skip(doc)
                BY ONLY <1>2, <2>5, Z3 DEF HandlePromiseRegisterListener, old
            <3>2. QED
                BY <3>1, SkipBoth, Isa
        <2>6. CASE IsExternal(old.promise) /\ old.promise.state = "pending"
            <3> DEFINE built ==
                    [old EXCEPT !.promise.listeners = @ \cup {ev.address}]
            <3>1. built = nw
                BY ONLY Z3 DEF built, nw, WithLs
            <3>2. HandlePromiseRegisterListener(ev, doc, t).doc
                    = Write(doc, ev.awaited, built)
                BY ONLY <1>2, <2>6, Z3
                   DEF HandlePromiseRegisterListener, old, built
            <3>3. DOMAIN Write(doc, ev.awaited, nw) = DOMAIN doc
                <4>1. DOMAIN Write(doc, ev.awaited, nw)
                        = (DOMAIN doc) \cup {ev.awaited}
                    BY ONLY WriteDom, Z3
                <4>2. QED
                    BY ONLY <1>2, <4>1, Z3
            <3>4. nw.promise.callbacks \subseteq DOMAIN doc
                BY ONLY <2>2, <2>3, <2>4, Z3
            <3>5. DocOk(Write(doc, ev.awaited, nw))
                <4>1. nw.promise.callbacks \subseteq (DOMAIN doc) \cup {ev.awaited}
                    BY ONLY <3>4, Z3
                <4>2. DocOk(doc) /\ Guard(nw)
                    BY <2>2, Z3 DEF DocOk
                <4>3. QED
                    BY ONLY <4>1, <4>2, WriteOk, Z3
            <3>6. Home(Write(doc, ev.awaited, nw), o)
                BY <3>3, SameHome, Isa
            <3>7. QED
                BY ONLY <3>1, <3>2, <3>5, <3>6, Z3
        <2>7. QED
            BY ONLY <2>5, <2>6, Z3
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3

LEMMA TCreateOk ==
    ASSUME NEW req, NEW doc, NEW t \in Nat, NEW o,
           DocOk(doc), Home(doc, o),
           req.ttl \in Ttl,
           req.action.id \in Id, req.action.id.origin = o
    PROVE  DocOk(HandleTaskCreate(req, doc, t).doc)
           /\ Home(HandleTaskCreate(req, doc, t).doc, o)
PROOF
    <1>1. CASE ~req.action.tags.targeted
        <2>1. HandleTaskCreate(req, doc, t) = Skip(doc)
            BY ONLY <1>1, Z3 DEF HandleTaskCreate
        <2>2. QED
            BY <2>1, SkipBoth, Isa
    <1>2. CASE req.action.tags.targeted /\ req.action.id \notin DOMAIN doc
        <2> DEFINE born == New(req.action, t)
        <2> DEFINE nw ==
                IF born.promise.state = "pending"
                THEN AcqOf(born, req.ttl, req.pid, t + req.ttl)
                ELSE born
        <2>1. born.promise.callbacks = {} /\ born.promise.listeners = {}
              /\ Guard(born)
            BY ONLY NewBits DEF born
        <2>2. Guard(nw) /\ nw.promise.callbacks = {}
            <3>1. CASE born.promise.state = "pending"
                <4>1. nw = AcqOf(born, req.ttl, req.pid, t + req.ttl)
                    BY ONLY <3>1, Z3 DEF nw
                <4>2. Guard(AcqOf(born, req.ttl, req.pid, t + req.ttl))
                      /\ AcqOf(born, req.ttl, req.pid, t + req.ttl).promise.callbacks
                           = born.promise.callbacks
                    BY <2>1, <3>1, AcqGuard, Z3
                <4>3. QED
                    BY ONLY <2>1, <4>1, <4>2, Z3
            <3>2. CASE born.promise.state /= "pending"
                BY ONLY <2>1, <3>2, Z3 DEF nw
            <3>3. QED
                BY ONLY <3>1, <3>2, Z3
        <2>3. HandleTaskCreate(req, doc, t).doc
                = Write(doc, req.action.id, nw)
            BY ONLY <1>2, Z3 DEF HandleTaskCreate, born, nw, AcqOf
        <2>4. DocOk(Write(doc, req.action.id, nw))
            <3>1. {} \subseteq (DOMAIN doc) \cup {req.action.id}
                BY ONLY Z3
            <3>2. QED
                BY <2>2, <3>1, WriteOk, Isa
        <2>5. Home(Write(doc, req.action.id, nw), o)
            BY WriteHome, Isa
        <2>6. QED
            BY ONLY <2>3, <2>4, <2>5, Z3
    <1>3. CASE req.action.tags.targeted /\ req.action.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.action.id], t)
        <2>1. CASE ~old.promise.tags.targeted \/ old.task.state /= "pending"
            <3>1. HandleTaskCreate(req, doc, t) = Skip(doc)
                BY ONLY <1>3, <2>1, Z3 DEF HandleTaskCreate, old
            <3>2. QED
                BY <3>1, SkipBoth, Isa
        <2>2. CASE old.promise.tags.targeted /\ old.task.state = "pending"
            <3> DEFINE nw == AcqOf(old, req.ttl, req.pid, t + req.ttl)
            <3>1. Project(doc[req.action.id], t) = doc[req.action.id]
                <4>1. CASE doc[req.action.id].promise.state = "pending"
                         /\ doc[req.action.id].promise.timeoutAt <= t
                    <5>1. old.task.state \in {"none", "fulfilled"}
                        BY ONLY <4>1, ProjFields, Z3 DEF old
                    <5>2. QED
                        BY ONLY <2>2, <5>1, Z3
                <4>2. CASE doc[req.action.id].promise.state /= "pending"
                         \/ ~(doc[req.action.id].promise.timeoutAt <= t)
                    BY ONLY <4>2, ProjId, Z3 DEF old
                <4>3. QED
                    BY ONLY <4>1, <4>2, Z3
            <3>2. Guard(doc[req.action.id])
                  /\ doc[req.action.id].promise.callbacks \subseteq DOMAIN doc
                BY <1>3, Isa DEF DocOk
            <3>3. old = doc[req.action.id]
                BY ONLY <3>1, Z3 DEF old
            <3>4. doc[req.action.id].promise.state = "pending"
                  /\ doc[req.action.id].promise.listeners \subseteq Address
                BY ONLY <2>2, <3>2, <3>3, Z3 DEF Guard
            <3>5. Guard(nw) /\ nw.promise.callbacks = old.promise.callbacks
                BY <3>3, <3>4, AcqGuard, Isa DEF nw
            <3>6. HandleTaskCreate(req, doc, t).doc
                    = Write(doc, req.action.id, nw)
                BY ONLY <1>3, <2>2, Z3 DEF HandleTaskCreate, old, nw, AcqOf
            <3>7. DOMAIN Write(doc, req.action.id, nw) = DOMAIN doc
                <4>1. DOMAIN Write(doc, req.action.id, nw)
                        = (DOMAIN doc) \cup {req.action.id}
                    BY WriteDom, Isa
                <4>2. QED
                    BY <1>3, <4>1, Isa
            <3>8. DocOk(Write(doc, req.action.id, nw))
                <4>1. nw.promise.callbacks \subseteq DOMAIN doc
                    BY ONLY <3>2, <3>3, <3>5, Z3
                <4>2. nw.promise.callbacks \subseteq (DOMAIN doc) \cup {req.action.id}
                    BY ONLY <4>1, Z3
                <4>3. DocOk(doc) /\ Guard(nw)
                    BY <3>5, Z3 DEF DocOk
                <4>4. QED
                    BY ONLY <4>2, <4>3, WriteOk, Z3
            <3>9. Home(Write(doc, req.action.id, nw), o)
                BY <3>7, SameHome, Isa
            <3>10. QED
                BY ONLY <3>6, <3>8, <3>9, Z3
        <2>3. QED
            BY ONLY <2>1, <2>2, Z3
    <1>4. QED
        BY ONLY <1>1, <1>2, <1>3, Z3

LEMMA AcqOk ==
    ASSUME NEW req, NEW doc, NEW t \in Nat, NEW o,
           DocOk(doc), Home(doc, o), req.ttl \in Ttl
    PROVE  DocOk(HandleTaskAcquire(req, doc, t).doc)
           /\ Home(HandleTaskAcquire(req, doc, t).doc, o)
PROOF
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. HandleTaskAcquire(req, doc, t) = Skip(doc)
            BY ONLY <1>1, Z3 DEF HandleTaskAcquire
        <2>2. QED
            BY <2>1, SkipBoth, Isa
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2> DEFINE skip ==
                \/ old.task.state /= "pending"
                \/ old.promise.state /= "pending"
                \/ old.task.version /= req.version
        <2>1. CASE skip
            <3>1. HandleTaskAcquire(req, doc, t) = Skip(doc)
                BY ONLY <1>2, <2>1, Z3 DEF HandleTaskAcquire, old, skip
            <3>2. QED
                BY <3>1, SkipBoth, Isa
        <2>2. CASE ~skip
            <3> DEFINE nw == AcqOf(old, req.ttl, req.pid, t + req.ttl)
            <3>1. old.task.state = "pending" /\ old.promise.state = "pending"
                BY ONLY <2>2, Z3 DEF skip
            <3>2. Project(doc[req.id], t) = doc[req.id]
                <4>1. CASE doc[req.id].promise.state = "pending"
                         /\ doc[req.id].promise.timeoutAt <= t
                    <5>1. old.task.state \in {"none", "fulfilled"}
                        BY ONLY <4>1, ProjFields, Z3 DEF old
                    <5>2. QED
                        BY ONLY <3>1, <5>1, Z3
                <4>2. CASE doc[req.id].promise.state /= "pending"
                         \/ ~(doc[req.id].promise.timeoutAt <= t)
                    BY ONLY <4>2, ProjId, Z3 DEF old
                <4>3. QED
                    BY ONLY <4>1, <4>2, Z3
            <3>3. old = doc[req.id]
                BY ONLY <3>2, Z3 DEF old
            <3>4. Guard(doc[req.id])
                  /\ doc[req.id].promise.callbacks \subseteq DOMAIN doc
                BY <1>2, Isa DEF DocOk
            <3>5. doc[req.id].promise.listeners \subseteq Address
                BY ONLY <3>4, Z3 DEF Guard
            <3>6. Guard(nw) /\ nw.promise.callbacks = old.promise.callbacks
                BY <3>1, <3>3, <3>5, AcqGuard, Isa DEF nw
            <3>7. HandleTaskAcquire(req, doc, t).doc = Write(doc, req.id, nw)
                BY ONLY <1>2, <2>2, Z3 DEF HandleTaskAcquire, old, nw, skip, AcqOf
            <3>8. DOMAIN Write(doc, req.id, nw) = DOMAIN doc
                <4>1. DOMAIN Write(doc, req.id, nw) = (DOMAIN doc) \cup {req.id}
                    BY WriteDom, Isa
                <4>2. QED
                    BY <1>2, <4>1, Isa
            <3>9. DocOk(Write(doc, req.id, nw))
                <4>1. nw.promise.callbacks \subseteq DOMAIN doc
                    BY ONLY <3>3, <3>4, <3>6, Z3
                <4>2. nw.promise.callbacks \subseteq (DOMAIN doc) \cup {req.id}
                    BY ONLY <4>1, Z3
                <4>3. DocOk(doc) /\ Guard(nw)
                    BY <3>6, Z3 DEF DocOk
                <4>4. QED
                    BY ONLY <4>2, <4>3, WriteOk, Z3
            <3>10. Home(Write(doc, req.id, nw), o)
                BY <3>8, SameHome, Isa
            <3>11. QED
                BY ONLY <3>7, <3>9, <3>10, Z3
        <2>3. QED
            BY ONLY <2>1, <2>2, Z3
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3

LEMMA FenceOk ==
    ASSUME NEW req, NEW doc, NEW t \in Nat, NEW o,
           DocOk(doc), Home(doc, o),
           req.id.origin = o,
           \/ /\ req.action.tag = "Create" /\ req.action.req \in CreateReq
           \/ /\ req.action.tag = "Settle" /\ req.action.req \in SettleReq
    PROVE  DocOk(HandleTaskFence(req, doc, t).doc)
           /\ Home(HandleTaskFence(req, doc, t).doc, o)
PROOF
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. HandleTaskFence(req, doc, t) = Skip(doc)
            BY ONLY <1>1, Z3 DEF HandleTaskFence
        <2>2. QED
            BY <2>1, SkipBoth, Isa
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2> DEFINE skip ==
                \/ req.action.req.id = req.id
                \/ req.action.req.id.origin /= req.id.origin
                \/ old.task.state /= "acquired"
                \/ old.promise.state /= "pending"
                \/ old.task.version /= req.version
        <2>1. CASE skip
            <3>1. HandleTaskFence(req, doc, t) = Skip(doc)
                BY ONLY <1>2, <2>1, Z3 DEF HandleTaskFence, old, skip
            <3>2. QED
                BY <3>1, SkipBoth, Isa
        <2>2. CASE ~skip /\ req.action.tag = "Create"
            <3>1. req.action.req.id \in Id
                <4>1. req.action.req \in CreateReq
                    BY <2>2, Z3
                <4>2. QED
                    BY ONLY <4>1, CreateId, Z3
            <3>2. req.action.req.id.origin = o
                BY <2>2, Isa DEF skip
            <3>3. HandleTaskFence(req, doc, t)
                    = HandlePromiseCreate(req.action.req, doc, t)
                BY ONLY <1>2, <2>2, Z3 DEF HandleTaskFence, old, skip
            <3>4. QED
                BY <3>1, <3>2, <3>3, CreateOk, Isa
        <2>3. CASE ~skip /\ req.action.tag /= "Create"
            <3>1. HandleTaskFence(req, doc, t)
                    = HandlePromiseSettle(req.action.req, doc, t)
                BY ONLY <1>2, <2>3, Z3 DEF HandleTaskFence, old, skip
            <3>2. QED
                <4>1. DocOk(doc) /\ Home(doc, o)
                    BY Z3 DEF DocOk, Home
                <4>2. QED
                    BY ONLY <3>1, <4>1, SettleOk, Z3
        <2>4. QED
            BY ONLY <2>1, <2>2, <2>3, Z3
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3

LEMMA RelOk ==
    ASSUME NEW req, NEW doc, NEW t \in Nat, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(HandleTaskRelease(req, doc, t).doc)
           /\ Home(HandleTaskRelease(req, doc, t).doc, o)
PROOF
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. HandleTaskRelease(req, doc, t) = Skip(doc)
            BY ONLY <1>1, Z3 DEF HandleTaskRelease
        <2>2. QED
            BY <2>1, SkipBoth, Isa
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2> DEFINE skip ==
                \/ old.task.state /= "acquired"
                \/ old.promise.state /= "pending"
                \/ old.task.version /= req.version
        <2>1. CASE skip
            <3>1. HandleTaskRelease(req, doc, t) = Skip(doc)
                BY ONLY <1>2, <2>1, Z3 DEF HandleTaskRelease, old, skip
            <3>2. QED
                BY <3>1, SkipBoth, Isa
        <2>2. CASE ~skip
            <3> DEFINE nw == PendOf(old, t)
            <3>1. old.task.state = "acquired" /\ old.promise.state = "pending"
                BY ONLY <2>2, Z3 DEF skip
            <3>2. Project(doc[req.id], t) = doc[req.id]
                <4>1. CASE doc[req.id].promise.state = "pending"
                         /\ doc[req.id].promise.timeoutAt <= t
                    <5>1. old.task.state \in {"none", "fulfilled"}
                        BY ONLY <4>1, ProjFields, Z3 DEF old
                    <5>2. QED
                        BY ONLY <3>1, <5>1, Z3
                <4>2. CASE doc[req.id].promise.state /= "pending"
                         \/ ~(doc[req.id].promise.timeoutAt <= t)
                    BY ONLY <4>2, ProjId, Z3 DEF old
                <4>3. QED
                    BY ONLY <4>1, <4>2, Z3
            <3>3. old = doc[req.id]
                BY ONLY <3>2, Z3 DEF old
            <3>4. Guard(doc[req.id])
                  /\ doc[req.id].promise.callbacks \subseteq DOMAIN doc
                BY <1>2, Isa DEF DocOk
            <3>5. doc[req.id].promise.listeners \subseteq Address
                BY ONLY <3>4, Z3 DEF Guard
            <3>6. Guard(nw) /\ nw.promise.callbacks = old.promise.callbacks
                BY <3>1, <3>3, <3>5, PendGuard, Isa DEF nw
            <3>7. HandleTaskRelease(req, doc, t).doc = Write(doc, req.id, nw)
                BY ONLY <1>2, <2>2, Z3 DEF HandleTaskRelease, old, nw, skip, PendOf
            <3>8. DOMAIN Write(doc, req.id, nw) = DOMAIN doc
                <4>1. DOMAIN Write(doc, req.id, nw) = (DOMAIN doc) \cup {req.id}
                    BY WriteDom, Isa
                <4>2. QED
                    BY <1>2, <4>1, Isa
            <3>9. DocOk(Write(doc, req.id, nw))
                <4>1. nw.promise.callbacks \subseteq DOMAIN doc
                    BY ONLY <3>3, <3>4, <3>6, Z3
                <4>2. nw.promise.callbacks \subseteq (DOMAIN doc) \cup {req.id}
                    BY ONLY <4>1, Z3
                <4>3. DocOk(doc) /\ Guard(nw)
                    BY <3>6, Z3 DEF DocOk
                <4>4. QED
                    BY ONLY <4>2, <4>3, WriteOk, Z3
            <3>10. Home(Write(doc, req.id, nw), o)
                BY <3>8, SameHome, Isa
            <3>11. QED
                BY ONLY <3>7, <3>9, <3>10, Z3
        <2>3. QED
            BY ONLY <2>1, <2>2, Z3
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3

LEMMA ContOk ==
    ASSUME NEW req, NEW doc, NEW t \in Nat, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(HandleTaskContinue(req, doc, t).doc)
           /\ Home(HandleTaskContinue(req, doc, t).doc, o)
PROOF
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. HandleTaskContinue(req, doc, t) = Skip(doc)
            BY ONLY <1>1, Z3 DEF HandleTaskContinue
        <2>2. QED
            BY <2>1, SkipBoth, Isa
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2> DEFINE skip ==
                \/ old.task.state /= "halted"
                \/ old.promise.state /= "pending"
        <2>1. CASE skip
            <3>1. HandleTaskContinue(req, doc, t) = Skip(doc)
                BY ONLY <1>2, <2>1, Z3 DEF HandleTaskContinue, old, skip
            <3>2. QED
                BY <3>1, SkipBoth, Isa
        <2>2. CASE ~skip
            <3> DEFINE nw == PendOf(old, t)
            <3>1. old.task.state = "halted" /\ old.promise.state = "pending"
                BY ONLY <2>2, Z3 DEF skip
            <3>2. Project(doc[req.id], t) = doc[req.id]
                <4>1. CASE doc[req.id].promise.state = "pending"
                         /\ doc[req.id].promise.timeoutAt <= t
                    <5>1. old.task.state \in {"none", "fulfilled"}
                        BY ONLY <4>1, ProjFields, Z3 DEF old
                    <5>2. QED
                        BY ONLY <3>1, <5>1, Z3
                <4>2. CASE doc[req.id].promise.state /= "pending"
                         \/ ~(doc[req.id].promise.timeoutAt <= t)
                    BY ONLY <4>2, ProjId, Z3 DEF old
                <4>3. QED
                    BY ONLY <4>1, <4>2, Z3
            <3>3. old = doc[req.id]
                BY ONLY <3>2, Z3 DEF old
            <3>4. Guard(doc[req.id])
                  /\ doc[req.id].promise.callbacks \subseteq DOMAIN doc
                BY <1>2, Isa DEF DocOk
            <3>5. doc[req.id].promise.listeners \subseteq Address
                BY ONLY <3>4, Z3 DEF Guard
            <3>6. Guard(nw) /\ nw.promise.callbacks = old.promise.callbacks
                BY <3>1, <3>3, <3>5, PendGuard, Isa DEF nw
            <3>7. HandleTaskContinue(req, doc, t).doc = Write(doc, req.id, nw)
                BY ONLY <1>2, <2>2, Z3 DEF HandleTaskContinue, old, nw, skip, PendOf
            <3>8. DOMAIN Write(doc, req.id, nw) = DOMAIN doc
                <4>1. DOMAIN Write(doc, req.id, nw) = (DOMAIN doc) \cup {req.id}
                    BY WriteDom, Isa
                <4>2. QED
                    BY <1>2, <4>1, Isa
            <3>9. DocOk(Write(doc, req.id, nw))
                <4>1. nw.promise.callbacks \subseteq DOMAIN doc
                    BY ONLY <3>3, <3>4, <3>6, Z3
                <4>2. nw.promise.callbacks \subseteq (DOMAIN doc) \cup {req.id}
                    BY ONLY <4>1, Z3
                <4>3. DocOk(doc) /\ Guard(nw)
                    BY <3>6, Z3 DEF DocOk
                <4>4. QED
                    BY ONLY <4>2, <4>3, WriteOk, Z3
            <3>10. Home(Write(doc, req.id, nw), o)
                BY <3>8, SameHome, Isa
            <3>11. QED
                BY ONLY <3>7, <3>9, <3>10, Z3
        <2>3. QED
            BY ONLY <2>1, <2>2, Z3
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3

LEMMA HaltOk ==
    ASSUME NEW req, NEW doc, NEW t, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(HandleTaskHalt(req, doc, t).doc)
           /\ Home(HandleTaskHalt(req, doc, t).doc, o)
PROOF
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. HandleTaskHalt(req, doc, t) = Skip(doc)
            BY ONLY <1>1, Z3 DEF HandleTaskHalt
        <2>2. QED
            BY <2>1, SkipBoth, Isa
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2> DEFINE skip ==
                \/ old.task.state = "none"
                \/ old.task.state \in {"fulfilled", "halted"}
        <2>1. CASE skip
            <3>1. HandleTaskHalt(req, doc, t) = Skip(doc)
                BY ONLY <1>2, <2>1, Z3 DEF HandleTaskHalt, old, skip
            <3>2. QED
                BY <3>1, SkipBoth, Isa
        <2>2. CASE ~skip
            <3> DEFINE nw == HaltOf(old)
            <3>1. old.task.state /= "none"
                  /\ old.task.state \notin {"fulfilled", "halted"}
                BY ONLY <2>2, Z3 DEF skip
            <3>2. Project(doc[req.id], t) = doc[req.id]
                <4>1. CASE doc[req.id].promise.state = "pending"
                         /\ doc[req.id].promise.timeoutAt <= t
                    <5>1. old.task.state \in {"none", "fulfilled"}
                        BY ONLY <4>1, ProjFields, Z3 DEF old
                    <5>2. QED
                        BY ONLY <3>1, <5>1, Z3
                <4>2. CASE doc[req.id].promise.state /= "pending"
                         \/ ~(doc[req.id].promise.timeoutAt <= t)
                    BY ONLY <4>2, ProjId, Z3 DEF old
                <4>3. QED
                    BY ONLY <4>1, <4>2, Z3
            <3>3. old = doc[req.id]
                BY ONLY <3>2, Z3 DEF old
            <3>4. Guard(doc[req.id])
                  /\ doc[req.id].promise.callbacks \subseteq DOMAIN doc
                BY <1>2, Isa DEF DocOk
            <3>5. nw.promise = old.promise /\ nw.task.state = "halted"
                BY ONLY HaltFields DEF nw
            <3>6. doc[req.id].promise.listeners \subseteq Address
                BY ONLY <3>4, Z3 DEF Guard
            <3>7. Guard(nw) /\ nw.promise.callbacks = old.promise.callbacks
                BY <3>3, <3>5, <3>6, Isa DEF Guard
            <3>8. HandleTaskHalt(req, doc, t).doc = Write(doc, req.id, nw)
                BY ONLY <1>2, <2>2, Z3 DEF HandleTaskHalt, old, nw, skip, HaltOf
            <3>9. DOMAIN Write(doc, req.id, nw) = DOMAIN doc
                <4>1. DOMAIN Write(doc, req.id, nw) = (DOMAIN doc) \cup {req.id}
                    BY WriteDom, Isa
                <4>2. QED
                    BY <1>2, <4>1, Isa
            <3>10. DocOk(Write(doc, req.id, nw))
                <4>1. nw.promise.callbacks \subseteq DOMAIN doc
                    BY ONLY <3>3, <3>4, <3>7, Z3
                <4>2. nw.promise.callbacks \subseteq (DOMAIN doc) \cup {req.id}
                    BY ONLY <4>1, Z3
                <4>3. DocOk(doc) /\ Guard(nw)
                    BY <3>7, Z3 DEF DocOk
                <4>4. QED
                    BY ONLY <4>2, <4>3, WriteOk, Z3
            <3>11. Home(Write(doc, req.id, nw), o)
                BY <3>9, SameHome, Isa
            <3>12. QED
                BY ONLY <3>8, <3>10, <3>11, Z3
        <2>3. QED
            BY ONLY <2>1, <2>2, Z3
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3

FulOf(obj, st, val, tm) ==
    [ promise |-> [obj.promise EXCEPT !.state = st,
                                       !.value = val,
                                       !.settledAt = tm],
      task    |-> [obj.task EXCEPT !.state          = "fulfilled",
                                   !.pid            = NoPid,
                                   !.ttl            = NoTime,
                                   !.leaseTimeoutAt = NoTime,
                                   !.retryTimeoutAt = NoTime,
                                   !.resumes        = {}] ]

LEMMA FulBody ==
    ASSUME NEW old, NEW st, NEW val, NEW tm, Guard(old)
    PROVE  Guard(FulOf(old, st, val, tm))
           /\ FulOf(old, st, val, tm).promise.callbacks = old.promise.callbacks
           /\ FulOf(old, st, val, tm).promise.listeners = old.promise.listeners
PROOF
    <1> DEFINE p1 == [old.promise EXCEPT !.state = st]
    <1> DEFINE p2 == [p1 EXCEPT !.value = val]
    <1> DEFINE p3 == [p2 EXCEPT !.settledAt = tm]
    <1> DEFINE k1 == [old.task EXCEPT !.state = "fulfilled"]
    <1> DEFINE k2 == [k1 EXCEPT !.pid = NoPid]
    <1> DEFINE k3 == [k2 EXCEPT !.ttl = NoTime]
    <1> DEFINE k4 == [k3 EXCEPT !.leaseTimeoutAt = NoTime]
    <1> DEFINE k5 == [k4 EXCEPT !.retryTimeoutAt = NoTime]
    <1> DEFINE k6 == [k5 EXCEPT !.resumes = {}]
    <1> DEFINE nw == [promise |-> p3, task |-> k6]
    <1>1. p1.callbacks = old.promise.callbacks
          /\ p1.listeners = old.promise.listeners
          /\ p1.state = st
        BY ONLY Z3 DEF p1
    <1>2. p2.callbacks = p1.callbacks /\ p2.listeners = p1.listeners
          /\ p2.state = p1.state
        BY ONLY Z3 DEF p2
    <1>3. p3.callbacks = p2.callbacks /\ p3.listeners = p2.listeners
          /\ p3.state = p2.state
        BY ONLY Z3 DEF p3
    <1>4. k1.state = "fulfilled"
        BY ONLY Z3 DEF k1
    <1>5. k2.state = k1.state
        BY ONLY Z3 DEF k2
    <1>6. k3.state = k2.state
        BY ONLY Z3 DEF k3
    <1>7. k4.state = k3.state
        BY ONLY Z3 DEF k4
    <1>8. k5.state = k4.state
        BY ONLY Z3 DEF k5
    <1>9. k6.state = k5.state
        BY ONLY Z3 DEF k6
    <1>10. nw.promise = p3 /\ nw.task = k6
        BY ONLY Z3 DEF nw
    <1>11. p3.callbacks = old.promise.callbacks
           /\ p3.listeners = old.promise.listeners
        BY ONLY <1>1, <1>2, <1>3, Z3
    <1>12. k6.state = "fulfilled"
        BY ONLY <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, Z3
    <1>13. nw.promise.callbacks = p3.callbacks
           /\ nw.promise.listeners = p3.listeners
           /\ nw.task.state = k6.state
        BY ONLY <1>10, Isa
    <1>14. FulOf(old, st, val, tm) = nw
        BY Zenon DEF FulOf, p1, p2, p3, k1, k2, k3, k4, k5, k6, nw
    <1>15. old.promise.listeners \subseteq Address
        BY Z3 DEF Guard
    <1>16. Guard(nw)
        BY ONLY <1>11, <1>12, <1>13, <1>15, Z3 DEF Guard
    <1>17. QED
        BY ONLY <1>11, <1>13, <1>14, <1>16, Z3

LEMMA FulOk ==
    ASSUME NEW req, NEW doc, NEW t, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(HandleTaskFulfill(req, doc, t).doc)
           /\ Home(HandleTaskFulfill(req, doc, t).doc, o)
PROOF
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. HandleTaskFulfill(req, doc, t) = Skip(doc)
            BY ONLY <1>1, Z3 DEF HandleTaskFulfill
        <2>2. QED
            BY <2>1, SkipBoth, Isa
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2> DEFINE skip ==
                \/ old.task.state /= "acquired"
                \/ old.promise.state /= "pending"
                \/ old.task.version /= req.version
        <2>1. CASE skip
            <3>1. HandleTaskFulfill(req, doc, t) = Skip(doc)
                BY ONLY <1>2, <2>1, Z3 DEF HandleTaskFulfill, old, skip
            <3>2. QED
                BY <3>1, SkipBoth, Isa
        <2>2. CASE ~skip
            <3> DEFINE nw == FulOf(old, req.action.state, req.action.value, t)
            <3>1. old.task.state = "acquired" /\ old.promise.state = "pending"
                BY ONLY <2>2, Z3 DEF skip
            <3>2. Project(doc[req.id], t) = doc[req.id]
                <4>1. CASE doc[req.id].promise.state = "pending"
                         /\ doc[req.id].promise.timeoutAt <= t
                    <5>1. old.task.state \in {"none", "fulfilled"}
                        BY ONLY <4>1, ProjFields, Z3 DEF old
                    <5>2. QED
                        BY ONLY <3>1, <5>1, Z3
                <4>2. CASE doc[req.id].promise.state /= "pending"
                         \/ ~(doc[req.id].promise.timeoutAt <= t)
                    BY ONLY <4>2, ProjId, Z3 DEF old
                <4>3. QED
                    BY ONLY <4>1, <4>2, Z3
            <3>3. old = doc[req.id]
                BY ONLY <3>2, Z3 DEF old
            <3>4. Guard(doc[req.id])
                  /\ doc[req.id].promise.callbacks \subseteq DOMAIN doc
                BY <1>2, Isa DEF DocOk
            <3>5. Guard(old)
                BY <3>3, <3>4, Z3 DEF Guard
            <3>6. Guard(nw) /\ nw.promise.callbacks = old.promise.callbacks
                BY <3>5, FulBody, Isa DEF nw
            <3>7. HandleTaskFulfill(req, doc, t).doc = Write(doc, req.id, nw)
                BY ONLY <1>2, <2>2, Z3
                   DEF HandleTaskFulfill, old, nw, skip, FulOf
            <3>8. DOMAIN Write(doc, req.id, nw) = DOMAIN doc
                <4>1. DOMAIN Write(doc, req.id, nw) = (DOMAIN doc) \cup {req.id}
                    BY WriteDom, Isa
                <4>2. QED
                    BY <1>2, <4>1, Isa
            <3>9. DocOk(Write(doc, req.id, nw))
                <4>1. nw.promise.callbacks \subseteq DOMAIN doc
                    BY ONLY <3>3, <3>4, <3>6, Z3
                <4>2. nw.promise.callbacks \subseteq (DOMAIN doc) \cup {req.id}
                    BY ONLY <4>1, Z3
                <4>3. DocOk(doc) /\ Guard(nw)
                    BY <3>6, Z3 DEF DocOk
                <4>4. QED
                    BY ONLY <4>2, <4>3, WriteOk, Z3
            <3>10. Home(Write(doc, req.id, nw), o)
                BY <3>8, SameHome, Isa
            <3>11. QED
                BY ONLY <3>7, <3>9, <3>10, Z3
        <2>3. QED
            BY ONLY <2>1, <2>2, Z3
    <1>3. QED
        BY ONLY <1>1, <1>2, Z3

LEMMA MemComp ==
    ASSUME NEW S, NEW P(_), NEW i
    PROVE  i \in {x \in S : P(x)} <=> (i \in S /\ P(i))
PROOF
    BY Isa

LeaseAt(obj, at) ==
    [obj EXCEPT !.task.leaseTimeoutAt = at]

LEMMA LeaseFields ==
    ASSUME NEW obj, NEW at
    PROVE  /\ LeaseAt(obj, at).promise = obj.promise
           /\ LeaseAt(obj, at).task.state = obj.task.state
           /\ LeaseAt(obj, at).task.ttl = obj.task.ttl
           /\ LeaseAt(obj, at).task.leaseTimeoutAt = at
PROOF
    <1> DEFINE k1 == [obj.task EXCEPT !.leaseTimeoutAt = at]
    <1> DEFINE nw == [obj EXCEPT !.task = k1]
    <1>1. k1.leaseTimeoutAt = at /\ k1.state = obj.task.state
          /\ k1.ttl = obj.task.ttl
        BY ONLY Z3 DEF k1
    <1>2. nw.task = k1 /\ nw.promise = obj.promise
        BY ONLY Z3 DEF nw
    <1>3. LeaseAt(obj, at) = nw
        BY Zenon DEF LeaseAt, k1, nw
    <1>4. nw.task.state = k1.state /\ nw.task.ttl = k1.ttl
          /\ nw.task.leaseTimeoutAt = k1.leaseTimeoutAt
          /\ nw.promise = obj.promise
        BY ONLY <1>2, Isa
    <1>5. QED
        BY ONLY <1>1, <1>3, <1>4, Z3

LEMMA LeaseGuard ==
    ASSUME NEW obj, NEW t \in Nat,
           obj.task.state = "acquired",
           obj.promise.state = "pending",
           obj.task.ttl \in Ttl,
           obj.promise.listeners \subseteq Address
    PROVE  Guard(LeaseAt(obj, t + obj.task.ttl))
           /\ LeaseAt(obj, t + obj.task.ttl).promise.callbacks
                = obj.promise.callbacks
PROOF
    <1> DEFINE nw == LeaseAt(obj, t + obj.task.ttl)
    <1>1. obj.task.state = "acquired" /\ obj.promise.state = "pending"
          /\ obj.task.ttl \in Ttl
          /\ obj.promise.listeners \subseteq Address
        BY Z3
    <1>2. nw.promise = obj.promise /\ nw.task.state = obj.task.state
          /\ nw.task.ttl = obj.task.ttl
          /\ nw.task.leaseTimeoutAt = t + obj.task.ttl
        BY ONLY LeaseFields DEF nw
    <1>3. nw.promise.state = obj.promise.state
          /\ nw.promise.listeners = obj.promise.listeners
          /\ nw.promise.callbacks = obj.promise.callbacks
        BY ONLY <1>2, Isa
    <1>4. nw.task.state = "acquired" /\ nw.task.ttl \in Ttl
          /\ nw.promise.state = "pending"
          /\ nw.promise.listeners \subseteq Address
          /\ nw.task.leaseTimeoutAt = t + obj.task.ttl
        BY ONLY <1>1, <1>2, <1>3, Z3
    <1>5. t + obj.task.ttl /= NoTime
        BY ONLY <1>1, LeaseTime, Z3
    <1>6. Guard(nw)
        BY ONLY <1>4, <1>5, Z3 DEF Guard
    <1>7. QED
        BY ONLY <1>3, <1>6, Z3

LEMMA BeatOk ==
    ASSUME NEW req, NEW doc, NEW t \in Nat, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(HandleTaskHeartbeat(req, doc, t).doc)
           /\ Home(HandleTaskHeartbeat(req, doc, t).doc, o)
PROOF
    <1>1. HIDE DEF SetToSeq
    <1> DEFINE beat ==
            { i \in DOMAIN doc :
                LET old == Project(doc[i], t)
                IN  /\ \E rf \in req.tasks :
                          rf.id = i /\ rf.version = old.task.version
                    /\ old.task.state = "acquired"
                    /\ old.task.pid = req.pid
                    /\ old.promise.state = "pending" }
    <1> DEFINE flat ==
            { i \in DOMAIN doc :
                /\ \E rf \in req.tasks :
                      rf.id = i
                      /\ rf.version = Project(doc[i], t).task.version
                /\ Project(doc[i], t).task.state = "acquired"
                /\ Project(doc[i], t).task.pid = req.pid
                /\ Project(doc[i], t).promise.state = "pending" }
    <1>2. beat = flat
        BY Z3 DEF beat, flat
    <1>3. CASE beat = {}
        <2>1. HandleTaskHeartbeat(req, doc, t) =
                LET beat ==
                        { i \in DOMAIN doc :
                            LET old == Project(doc[i], t)
                            IN  /\ \E rf \in req.tasks :
                                      rf.id = i /\ rf.version = old.task.version
                                /\ old.task.state = "acquired"
                                /\ old.task.pid = req.pid
                                /\ old.promise.state = "pending" }
                    q == SetToSeq({ i \in beat :
                                      t + doc[i].task.ttl
                                          /= doc[i].task.leaseTimeoutAt })
                IN IF beat = {} THEN Skip(doc)
                   ELSE [ doc |->
                            [ i \in DOMAIN doc |->
                                IF i \in beat THEN
                                    LET old == Project(doc[i], t)
                                    IN [old EXCEPT !.task.leaseTimeoutAt =
                                                      t + old.task.ttl]
                                ELSE doc[i] ],
                          puts |->
                            [ n \in 1 .. Len(q) |->
                                [at |-> t + doc[q[n]].task.ttl,
                                 id |-> q[n], kind |-> "lease"] ],
                          dels |->
                            [ n \in 1 .. Len(q) |->
                                [at |-> doc[q[n]].task.leaseTimeoutAt,
                                 id |-> q[n], kind |-> "lease"] ],
                          sends |-> << >> ]
            BY ONLY DEF HandleTaskHeartbeat
        <2>2. HandleTaskHeartbeat(req, doc, t).doc = doc
            BY <1>3, <2>1, Isa DEF beat, Skip
        <2>3. DocOk(doc) /\ Home(doc, o)
            BY Z3 DEF DocOk, Home
        <2>4. QED
            BY <2>2, <2>3, Isa
    <1>4. CASE beat /= {}
        <2> DEFINE img ==
                [ i \in DOMAIN doc |->
                    IF i \in beat THEN
                        LET old == Project(doc[i], t)
                        IN  [old EXCEPT !.task.leaseTimeoutAt =
                                            t + old.task.ttl]
                    ELSE
                        doc[i] ]
        <2>1. HandleTaskHeartbeat(req, doc, t).doc = img
            BY ONLY <1>4, Z3 DEF HandleTaskHeartbeat, beat, img
        <2>2. DOMAIN img = DOMAIN doc
            BY DomCtor, Isa DEF img
        <2>3. ASSUME NEW i \in DOMAIN doc
              PROVE  img[i].promise.callbacks \subseteq DOMAIN doc
                     /\ Guard(img[i])
            <3>1. img[i] =
                    IF i \in beat THEN
                        LET old == Project(doc[i], t)
                        IN  [old EXCEPT !.task.leaseTimeoutAt =
                                            t + old.task.ttl]
                    ELSE
                        doc[i]
                BY AppCtor, Isa DEF img
            <3>2. CASE i \notin beat
                <4>1. img[i] = doc[i]
                    BY ONLY <3>1, <3>2, Z3
                <4>2. doc[i].promise.callbacks \subseteq DOMAIN doc
                      /\ Guard(doc[i])
                    BY Isa DEF DocOk
                <4>3. img[i].promise.callbacks = doc[i].promise.callbacks
                      /\ (Guard(img[i]) <=> Guard(doc[i]))
                    BY ONLY <4>1, Isa
                <4>4. QED
                    BY ONLY <4>2, <4>3, Z3
            <3>3. CASE i \in beat
                <4> DEFINE old == Project(doc[i], t)
                <4> DEFINE nw == LeaseAt(doc[i], t + doc[i].task.ttl)
                <4>1. i \in flat
                    BY ONLY <1>2, <3>3, Z3 DEF beat
                <4>2. i \in DOMAIN doc
                      /\ old.task.state = "acquired"
                      /\ old.task.pid = req.pid
                      /\ old.promise.state = "pending"
                    BY <4>1, MemComp, Isa DEF flat, old
                <4>3. Project(doc[i], t) = doc[i]
                    <5>1. CASE doc[i].promise.state = "pending"
                             /\ doc[i].promise.timeoutAt <= t
                        <6>1. old.task.state \in {"none", "fulfilled"}
                            BY ONLY <5>1, ProjFields, Z3 DEF old
                        <6>2. QED
                            BY ONLY <4>2, <6>1, Z3
                    <5>2. CASE doc[i].promise.state /= "pending"
                             \/ ~(doc[i].promise.timeoutAt <= t)
                        BY ONLY <5>2, ProjId, Z3 DEF old
                    <5>3. QED
                        BY ONLY <5>1, <5>2, Z3
                <4>4. old = doc[i]
                    BY ONLY <4>3, Z3 DEF old
                <4>5. Guard(doc[i])
                      /\ doc[i].promise.callbacks \subseteq DOMAIN doc
                    BY Isa DEF DocOk
                <4>6. doc[i].task.state = "acquired"
                      /\ doc[i].promise.state = "pending"
                      /\ doc[i].task.ttl \in Ttl
                      /\ doc[i].promise.listeners \subseteq Address
                    BY ONLY <4>2, <4>4, <4>5, Z3 DEF Guard
                <4>7. Guard(nw)
                      /\ nw.promise.callbacks = doc[i].promise.callbacks
                    BY <4>6, LeaseGuard, Isa DEF nw
                <4>8. img[i] = nw
                    <5> DEFINE touched ==
                            [old EXCEPT !.task.leaseTimeoutAt = t + old.task.ttl]
                    <5> DEFINE raw ==
                            [doc[i] EXCEPT !.task.leaseTimeoutAt =
                                              t + doc[i].task.ttl]
                    <5>1. img[i] = touched
                        BY ONLY <3>1, <3>3, Z3 DEF touched, old
                    <5>2. touched = raw
                        BY ONLY <4>4, Isa DEF touched, raw, old
                    <5>3. raw = nw
                        BY Zenon DEF raw, nw, LeaseAt
                    <5>4. QED
                        BY ONLY <5>1, <5>2, <5>3, Z3
                <4>9. img[i].promise.callbacks = nw.promise.callbacks
                      /\ (Guard(img[i]) <=> Guard(nw))
                    BY ONLY <4>8, Isa
                <4>10. QED
                    BY ONLY <4>5, <4>7, <4>9, Z3
            <3>4. QED
                BY ONLY <3>2, <3>3, Z3
        <2>4. DocOk(img)
            BY <2>2, <2>3, Isa DEF DocOk
        <2>5. Home(img, o)
            BY <2>2, SameHome, Isa
        <2>6. QED
            BY ONLY <2>1, <2>4, <2>5, Z3
    <1>5. QED
        BY ONLY <1>3, <1>4, Z3

LEMMA SusGuard ==
    ASSUME NEW obj, Guard(obj), obj.promise.state = "pending"
    PROVE  Guard(SusOf(obj))
           /\ SusOf(obj).promise.callbacks = obj.promise.callbacks
PROOF
    <1> DEFINE nw == SusOf(obj)
    <1>1. nw.promise = obj.promise /\ nw.task.state = "suspended"
        BY ONLY SusFields DEF nw
    <1>2. nw.promise.callbacks = obj.promise.callbacks
          /\ nw.promise.listeners = obj.promise.listeners
          /\ nw.promise.state = obj.promise.state
        BY ONLY <1>1, Isa
    <1>3. obj.promise.state = "pending"
          /\ obj.promise.listeners \subseteq Address
        BY Z3 DEF Guard
    <1>4. nw.promise.state = "pending"
          /\ nw.promise.listeners \subseteq Address
          /\ nw.task.state = "suspended"
          /\ nw.promise.callbacks = obj.promise.callbacks
        BY ONLY <1>1, <1>2, <1>3, Z3
    <1>5. QED
        BY ONLY <1>4, Z3 DEF Guard

ClearRes(obj) ==
    [obj EXCEPT !.task.resumes = {}]

LEMMA ClearFields ==
    ASSUME NEW obj
    PROVE  /\ ClearRes(obj).promise = obj.promise
           /\ ClearRes(obj).task.state = obj.task.state
           /\ ClearRes(obj).task.ttl = obj.task.ttl
           /\ ClearRes(obj).task.leaseTimeoutAt = obj.task.leaseTimeoutAt
           /\ ClearRes(obj).task.retryTimeoutAt = obj.task.retryTimeoutAt
PROOF
    <1> DEFINE k1 == [obj.task EXCEPT !.resumes = {}]
    <1> DEFINE nw == [obj EXCEPT !.task = k1]
    <1>1. k1.resumes = {} /\ k1.state = obj.task.state
          /\ k1.ttl = obj.task.ttl
          /\ k1.leaseTimeoutAt = obj.task.leaseTimeoutAt
          /\ k1.retryTimeoutAt = obj.task.retryTimeoutAt
        BY ONLY Z3 DEF k1
    <1>2. nw.task = k1 /\ nw.promise = obj.promise
        BY ONLY Z3 DEF nw
    <1>3. ClearRes(obj) = nw
        BY Zenon DEF ClearRes, k1, nw
    <1>4. nw.task.state = k1.state /\ nw.task.ttl = k1.ttl
          /\ nw.task.leaseTimeoutAt = k1.leaseTimeoutAt
          /\ nw.task.retryTimeoutAt = k1.retryTimeoutAt
          /\ nw.promise = obj.promise
        BY ONLY <1>2, Isa
    <1>5. QED
        BY ONLY <1>1, <1>3, <1>4, Z3

LEMMA ClearGuard ==
    ASSUME NEW obj, Guard(obj)
    PROVE  Guard(ClearRes(obj))
           /\ ClearRes(obj).promise.callbacks = obj.promise.callbacks
PROOF
    <1> DEFINE nw == ClearRes(obj)
    <1>1. nw.promise = obj.promise /\ nw.task.state = obj.task.state
          /\ nw.task.ttl = obj.task.ttl
          /\ nw.task.leaseTimeoutAt = obj.task.leaseTimeoutAt
          /\ nw.task.retryTimeoutAt = obj.task.retryTimeoutAt
        BY ONLY ClearFields DEF nw
    <1>2. nw.promise.callbacks = obj.promise.callbacks
          /\ nw.promise.listeners = obj.promise.listeners
          /\ nw.promise.state = obj.promise.state
        BY ONLY <1>1, Isa
    <1>3. obj.task.state = "acquired" =>
                /\ obj.task.leaseTimeoutAt /= NoTime
                /\ obj.task.ttl \in Ttl
                /\ obj.promise.state = "pending"
          /\ obj.task.state = "pending" =>
                /\ obj.task.retryTimeoutAt /= NoTime
                /\ obj.promise.state = "pending"
          /\ obj.task.state = "suspended" => obj.promise.state = "pending"
          /\ obj.promise.listeners \subseteq Address
        BY Z3 DEF Guard
    <1>4. QED
        BY <1>1, <1>2, <1>3, Isa DEF Guard, nw

LEMMA SusOk ==
    ASSUME NEW req, NEW doc, NEW t, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(HandleTaskSuspend(req, doc, t).doc)
           /\ Home(HandleTaskSuspend(req, doc, t).doc, o)
PROOF
    <1>1. HandleTaskSuspend(req, doc, t) =
            LET aw   == { a.awaited : a \in req.actions }
                seen == { a \in aw : a \in DOMAIN doc }
            IN IF \/ req.actions = {}
                  \/ req.id \in aw
                  \/ \E a \in aw : a.origin /= req.id.origin
                  \/ req.id \notin DOMAIN doc
                  \/ seen /= aw
               THEN Skip(doc)
               ELSE LET old == Project(doc[req.id], t)
                        new == [old EXCEPT !.task.state          = "suspended",
                                           !.task.pid            = NoPid,
                                           !.task.ttl            = NoTime,
                                           !.task.leaseTimeoutAt = NoTime,
                                           !.task.retryTimeoutAt = NoTime,
                                           !.task.resumes        = {}]
                    IN IF \/ old.task.state /= "acquired"
                          \/ old.promise.state /= "pending"
                          \/ old.task.version /= req.version
                          \/ \E a \in aw :
                                ~IsExternal(Project(doc[a], t).promise)
                       THEN Skip(doc)
                       ELSE IF \E a \in aw :
                                 Project(doc[a], t).promise.state /= "pending"
                            THEN [ doc |->
                                     Write(doc, req.id,
                                           [old EXCEPT !.task.resumes = {}]),
                                   puts |-> << >>,
                                   dels |-> << >>,
                                   sends |-> << >> ]
                            ELSE [ doc |->
                                     [ i \in DOMAIN doc |->
                                         IF i = req.id THEN new
                                         ELSE IF i \in aw THEN
                                             [Project(doc[i], t) EXCEPT
                                                  !.promise.callbacks =
                                                      @ \cup {req.id}]
                                         ELSE doc[i] ],
                                   puts |-> << >>,
                                   dels |->
                                     << [at |-> old.task.leaseTimeoutAt,
                                         id |-> req.id, kind |-> "lease"] >>,
                                   sends |-> << >> ]
        BY ONLY DEF HandleTaskSuspend
    <1> DEFINE aw == { a.awaited : a \in req.actions }
    <1> DEFINE seen == { a \in aw : a \in DOMAIN doc }
    <1> DEFINE outer ==
            \/ req.actions = {}
            \/ req.id \in aw
            \/ \E a \in aw : a.origin /= req.id.origin
            \/ req.id \notin DOMAIN doc
            \/ seen /= aw
    <1>2. CASE outer
        <2>1. HandleTaskSuspend(req, doc, t).doc = doc
            BY <1>1, <1>2, Isa DEF aw, seen, outer, Skip
        <2>2. DocOk(doc) /\ Home(doc, o)
            BY Z3 DEF DocOk, Home
        <2>3. QED
            BY <2>1, <2>2, Isa
    <1>3. CASE ~outer
        <2> DEFINE old == Project(doc[req.id], t)
        <2> DEFINE inner ==
                \/ old.task.state /= "acquired"
                \/ old.promise.state /= "pending"
                \/ old.task.version /= req.version
                \/ \E a \in aw : ~IsExternal(Project(doc[a], t).promise)
        <2> DEFINE late ==
                \E a \in aw : Project(doc[a], t).promise.state /= "pending"
        <2>1. req.id \in DOMAIN doc /\ req.id \notin aw /\ seen = aw
              /\ aw \subseteq DOMAIN doc
            BY <1>3, Isa DEF outer, aw, seen
        <2>2. CASE inner
            <3>1. HandleTaskSuspend(req, doc, t).doc = doc
                BY <1>1, <1>3, <2>2, Isa DEF aw, seen, old, outer, inner, Skip
            <3>2. DocOk(doc) /\ Home(doc, o)
                BY Z3 DEF DocOk, Home
            <3>3. QED
                BY <3>1, <3>2, Isa
        <2>3. CASE ~inner /\ late
            <3> DEFINE cleared == [old EXCEPT !.task.resumes = {}]
            <3> DEFINE nw == ClearRes(old)
            <3>1. HandleTaskSuspend(req, doc, t).doc
                    = Write(doc, req.id, cleared)
                BY ONLY <1>1, <1>3, <2>3, Z3
                   DEF aw, seen, old, outer, inner, late, cleared
            <3>2. cleared = nw
                BY Zenon DEF cleared, nw, ClearRes, old
            <3>3. old.task.state = "acquired" /\ old.promise.state = "pending"
                BY ONLY <2>3, Z3 DEF inner
            <3>4. Project(doc[req.id], t) = doc[req.id]
                <4>1. CASE doc[req.id].promise.state = "pending"
                         /\ doc[req.id].promise.timeoutAt <= t
                    <5>1. old.task.state \in {"none", "fulfilled"}
                        BY ONLY <4>1, ProjFields, Z3 DEF old
                    <5>2. QED
                        BY ONLY <3>3, <5>1, Z3
                <4>2. CASE doc[req.id].promise.state /= "pending"
                         \/ ~(doc[req.id].promise.timeoutAt <= t)
                    BY ONLY <4>2, ProjId, Z3 DEF old
                <4>3. QED
                    BY ONLY <4>1, <4>2, Z3
            <3>5. old = doc[req.id]
                BY ONLY <3>4, Z3 DEF old
            <3>6. Guard(doc[req.id])
                  /\ doc[req.id].promise.callbacks \subseteq DOMAIN doc
                <4>1. DocOk(doc) /\ req.id \in DOMAIN doc
                    BY <2>1, Z3 DEF DocOk
                <4>2. QED
                    BY ONLY <4>1, Isa DEF DocOk
            <3>7. Guard(nw) /\ nw.promise.callbacks = old.promise.callbacks
                BY <3>5, <3>6, ClearGuard, Isa DEF nw
            <3>8. DOMAIN Write(doc, req.id, nw) = DOMAIN doc
                <4>1. DOMAIN Write(doc, req.id, nw) = (DOMAIN doc) \cup {req.id}
                    BY WriteDom, Isa
                <4>2. QED
                    BY <2>1, <4>1, Isa
            <3>9. DocOk(Write(doc, req.id, nw))
                <4>1. nw.promise.callbacks \subseteq DOMAIN doc
                    BY ONLY <3>5, <3>6, <3>7, Z3
                <4>2. nw.promise.callbacks \subseteq (DOMAIN doc) \cup {req.id}
                    BY ONLY <4>1, Z3
                <4>3. DocOk(doc) /\ Guard(nw)
                    BY <3>7, Z3 DEF DocOk
                <4>4. QED
                    BY ONLY <4>2, <4>3, WriteOk, Z3
            <3>10. Home(Write(doc, req.id, nw), o)
                BY <3>8, SameHome, Isa
            <3>11. Write(doc, req.id, cleared) = Write(doc, req.id, nw)
                BY ONLY <3>2, Z3
            <3>12. QED
                BY <3>1, <3>9, <3>10, <3>11, Isa
        <2>4. CASE ~inner /\ ~late
            <3> DEFINE img ==
                    [ i \in DOMAIN doc |->
                        IF i = req.id THEN
                            [old EXCEPT !.task.state          = "suspended",
                                        !.task.pid            = NoPid,
                                        !.task.ttl            = NoTime,
                                        !.task.leaseTimeoutAt = NoTime,
                                        !.task.retryTimeoutAt = NoTime,
                                        !.task.resumes        = {}]
                        ELSE IF i \in aw THEN
                            [Project(doc[i], t) EXCEPT
                                 !.promise.callbacks = @ \cup {req.id}]
                        ELSE doc[i] ]
            <3>1. HandleTaskSuspend(req, doc, t).doc = img
                BY ONLY <1>1, <1>3, <2>4, Z3
                   DEF aw, seen, old, outer, inner, late, img
            <3>2. DOMAIN img = DOMAIN doc
                BY DomCtor, Isa DEF img
            <3>3. old.task.state = "acquired" /\ old.promise.state = "pending"
                BY ONLY <2>4, Z3 DEF inner
            <3>4. Project(doc[req.id], t) = doc[req.id]
                <4>1. CASE doc[req.id].promise.state = "pending"
                         /\ doc[req.id].promise.timeoutAt <= t
                    <5>1. old.task.state \in {"none", "fulfilled"}
                        BY ONLY <4>1, ProjFields, Z3 DEF old
                    <5>2. QED
                        BY ONLY <3>3, <5>1, Z3
                <4>2. CASE doc[req.id].promise.state /= "pending"
                         \/ ~(doc[req.id].promise.timeoutAt <= t)
                    BY ONLY <4>2, ProjId, Z3 DEF old
                <4>3. QED
                    BY ONLY <4>1, <4>2, Z3
            <3>5. old = doc[req.id]
                BY ONLY <3>4, Z3 DEF old
            <3>6. \A a \in aw : Project(doc[a], t).promise.state = "pending"
                BY ONLY <2>4, Z3 DEF late
            <3>7. ASSUME NEW i \in DOMAIN doc
                  PROVE  img[i].promise.callbacks \subseteq DOMAIN doc
                         /\ Guard(img[i])
                <4>1. img[i] =
                        IF i = req.id THEN
                            [old EXCEPT !.task.state          = "suspended",
                                        !.task.pid            = NoPid,
                                        !.task.ttl            = NoTime,
                                        !.task.leaseTimeoutAt = NoTime,
                                        !.task.retryTimeoutAt = NoTime,
                                        !.task.resumes        = {}]
                        ELSE IF i \in aw THEN
                            [Project(doc[i], t) EXCEPT
                                 !.promise.callbacks = @ \cup {req.id}]
                        ELSE doc[i]
                    BY AppCtor, Isa DEF img
                <4>2. CASE i = req.id
                    <5> DEFINE built ==
                            [old EXCEPT !.task.state          = "suspended",
                                        !.task.pid            = NoPid,
                                        !.task.ttl            = NoTime,
                                        !.task.leaseTimeoutAt = NoTime,
                                        !.task.retryTimeoutAt = NoTime,
                                        !.task.resumes        = {}]
                    <5> DEFINE nw == SusOf(old)
                    <5>1. img[i] = built
                        BY ONLY <4>1, <4>2, Z3 DEF built
                    <5>2. built = nw
                        BY Zenon DEF built, nw, SusOf, old
                    <5>3. Guard(doc[req.id])
                          /\ doc[req.id].promise.callbacks \subseteq DOMAIN doc
                        <6>1. DocOk(doc) /\ req.id \in DOMAIN doc
                            BY <2>1, Z3 DEF DocOk
                        <6>2. QED
                            BY ONLY <6>1, Isa DEF DocOk
                    <5>4. Guard(nw)
                          /\ nw.promise.callbacks = old.promise.callbacks
                        BY <3>3, <3>5, <5>3, SusGuard, Isa DEF nw
                    <5>5. img[i].promise.callbacks = nw.promise.callbacks
                          /\ (Guard(img[i]) <=> Guard(nw))
                        BY ONLY <5>1, <5>2, Isa
                    <5>6. QED
                        BY ONLY <3>5, <5>3, <5>4, <5>5, Z3
                <4>3. CASE i /= req.id /\ i \in aw
                    <5> DEFINE proj == Project(doc[i], t)
                    <5> DEFINE built ==
                            [proj EXCEPT !.promise.callbacks = @ \cup {req.id}]
                    <5> DEFINE nw ==
                            WithCb(proj, proj.promise.callbacks \cup {req.id})
                    <5>1. img[i] = built
                        BY ONLY <4>1, <4>3, Z3 DEF built, proj
                    <5>2. built = nw
                        BY ONLY Z3 DEF built, nw, WithCb, proj
                    <5>3. proj.promise.state = "pending"
                        BY ONLY <3>6, <4>3, Z3 DEF proj
                    <5>4. Project(doc[i], t) = doc[i]
                        <6>1. CASE doc[i].promise.state = "pending"
                                 /\ doc[i].promise.timeoutAt <= t
                            <7>1. proj.promise.state \in
                                    {"resolved", "rejectedTimedout"}
                                BY ONLY <6>1, ProjFields, Z3 DEF proj
                            <7>2. QED
                                BY ONLY <5>3, <7>1, Z3
                        <6>2. CASE doc[i].promise.state /= "pending"
                                 \/ ~(doc[i].promise.timeoutAt <= t)
                            BY ONLY <6>2, ProjId, Z3 DEF proj
                        <6>3. QED
                            BY ONLY <6>1, <6>2, Z3
                    <5>5. proj = doc[i]
                        BY ONLY <5>4, Z3 DEF proj
                    <5>6. Guard(doc[i])
                          /\ doc[i].promise.callbacks \subseteq DOMAIN doc
                        BY Isa DEF DocOk
                    <5>7. nw.promise.callbacks
                            = proj.promise.callbacks \cup {req.id}
                          /\ nw.promise.state = proj.promise.state
                          /\ nw.task = proj.task
                        BY ONLY CbFields DEF nw
                    <5>8. Guard(nw)
                        <6>1. proj.promise.callbacks \cup {req.id}
                                \subseteq proj.promise.callbacks \cup {req.id}
                            BY Z3
                        <6>2. Guard(proj)
                            BY <5>5, <5>6, Z3 DEF Guard, proj
                        <6>3. QED
                            BY ONLY <6>1, <6>2, CbGuard, Z3 DEF nw
                    <5>9. nw.promise.callbacks \subseteq DOMAIN doc
                        BY ONLY <2>1, <5>5, <5>6, <5>7, Z3
                    <5>10. img[i].promise.callbacks = nw.promise.callbacks
                           /\ (Guard(img[i]) <=> Guard(nw))
                        BY ONLY <5>1, <5>2, Isa
                    <5>11. QED
                        BY ONLY <5>8, <5>9, <5>10, Z3
                <4>4. CASE i /= req.id /\ i \notin aw
                    <5>1. img[i] = doc[i]
                        BY ONLY <4>1, <4>4, Z3
                    <5>2. doc[i].promise.callbacks \subseteq DOMAIN doc
                          /\ Guard(doc[i])
                        BY Isa DEF DocOk
                    <5>3. img[i].promise.callbacks = doc[i].promise.callbacks
                          /\ (Guard(img[i]) <=> Guard(doc[i]))
                        BY ONLY <5>1, Isa
                    <5>4. QED
                        BY ONLY <5>2, <5>3, Z3
                <4>5. QED
                    BY ONLY <4>2, <4>3, <4>4, Z3
            <3>8. DocOk(img)
                BY <3>2, <3>7, Isa DEF DocOk
            <3>9. Home(img, o)
                BY <3>2, SameHome, Isa
            <3>10. QED
                BY ONLY <3>1, <3>8, <3>9, Z3
        <2>5. QED
            BY ONLY <2>2, <2>3, <2>4, Z3
    <1>4. QED
        BY ONLY <1>2, <1>3, Z3

HandleTag ==
    { "PromiseCreate", "PromiseSettle",
      "PromiseRegisterCallback", "PromiseRegisterListener",
      "TaskCreate", "TaskAcquire", "TaskFence",
      "TaskHeartbeat", "TaskSuspend", "TaskFulfill",
      "TaskRelease", "TaskHalt", "TaskContinue", "Timeout" }

LEMMA AcqTtl ==
    ASSUME NEW ev \in Event, ev.tag = "TaskAcquire"
    PROVE  ev.ttl \in Ttl
PROOF
    BY Z3 DEF Event, ExternalEvent, InternalEvent, On

LEMMA LsAddr ==
    ASSUME NEW ev \in Event, ev.tag = "PromiseRegisterListener"
    PROVE  ev.address \in Address
PROOF
    BY Z3 DEF Event, ExternalEvent, InternalEvent, On

LEMMA CreateOf ==
    ASSUME NEW ev \in Event, ev.tag = "PromiseCreate"
    PROVE  ev.req \in CreateReq
PROOF
    BY Z3 DEF Event, ExternalEvent, InternalEvent, On

LEMMA TCreateOf ==
    ASSUME NEW ev \in Event, ev.tag = "TaskCreate"
    PROVE  ev.ttl \in Ttl /\ ev.action \in CreateReq
PROOF
    BY Z3 DEF Event, ExternalEvent, InternalEvent, On

LEMMA FenceOf ==
    ASSUME NEW ev \in Event, ev.tag = "TaskFence"
    PROVE  \/ /\ ev.action.tag = "Create" /\ ev.action.req \in CreateReq
           \/ /\ ev.action.tag = "Settle" /\ ev.action.req \in SettleReq
PROOF
    BY Z3 DEF Event, ExternalEvent, InternalEvent, On, FenceAction

LEMMA HandleOk ==
    ASSUME NEW ev, NEW doc, NEW t \in Nat, NEW o,
           DocOk(doc), Home(doc, o),
           ev \in Event, ev.tag \in HandleTag, OriginOf(ev) = o
    PROVE  DocOk(Handle(ev, doc, t).doc)
           /\ Home(Handle(ev, doc, t).doc, o)
PROOF
    <1>2. CASE ev.tag = "PromiseCreate"
        <2>1. Handle(ev, doc, t) = HandlePromiseCreate(ev.req, doc, t)
            BY ONLY <1>2, Z3 DEF Handle
        <2>2. ev.req \in CreateReq
            BY <1>2, CreateOf, Z3
        <2>3. ev.req.id \in Id
            BY ONLY <2>2, CreateId, Z3
        <2>4. ev.req.id.origin = o
            BY <1>2, Z3 DEF OriginOf
        <2>5. QED
            BY <2>1, <2>3, <2>4, CreateOk, Isa
    <1>3. CASE ev.tag = "PromiseSettle"
        <2>1. Handle(ev, doc, t) = HandlePromiseSettle(ev.req, doc, t)
            BY ONLY <1>3, Z3 DEF Handle
        <2>2. QED
            BY <2>1, SettleOk, Isa
    <1>4. CASE ev.tag = "PromiseRegisterCallback"
        <2>1. Handle(ev, doc, t)
                = HandlePromiseRegisterCallback(ev.req, doc, t)
            BY ONLY <1>4, Z3 DEF Handle
        <2>2. QED
            BY <2>1, RegCbOk, Isa
    <1>5. CASE ev.tag = "PromiseRegisterListener"
        <2>1. Handle(ev, doc, t)
                = HandlePromiseRegisterListener(ev, doc, t)
            BY ONLY <1>5, Z3 DEF Handle
        <2>2. ev.address \in Address
            BY <1>5, LsAddr, Z3
        <2>3. QED
            BY <2>1, <2>2, RegLsOk, Isa
    <1>7. CASE ev.tag = "TaskCreate"
        <2>1. Handle(ev, doc, t) = HandleTaskCreate(ev, doc, t)
            BY ONLY <1>7, Z3 DEF Handle
        <2>2. ev.action \in CreateReq /\ ev.ttl \in Ttl
            BY <1>7, TCreateOf, Z3
        <2>3. ev.action.id \in Id
            BY ONLY <2>2, CreateId, Z3
        <2>4. ev.action.id.origin = o
            BY <1>7, Z3 DEF OriginOf
        <2>5. QED
            BY <2>1, <2>2, <2>3, <2>4, TCreateOk, Isa
    <1>8. CASE ev.tag = "TaskAcquire"
        <2>1. Handle(ev, doc, t) = HandleTaskAcquire(ev, doc, t)
            BY ONLY <1>8, Z3 DEF Handle
        <2>2. ev.ttl \in Ttl
            BY <1>8, AcqTtl, Z3
        <2>3. QED
            BY <2>1, <2>2, AcqOk, Isa
    <1>9. CASE ev.tag = "TaskFence"
        <2>1. Handle(ev, doc, t) = HandleTaskFence(ev, doc, t)
            BY ONLY <1>9, Z3 DEF Handle
        <2>2. ev.id.origin = o
            BY <1>9, Z3 DEF OriginOf
        <2>3. \/ /\ ev.action.tag = "Create" /\ ev.action.req \in CreateReq
              \/ /\ ev.action.tag = "Settle" /\ ev.action.req \in SettleReq
            BY <1>9, FenceOf, Z3
        <2>4. QED
            BY <2>1, <2>2, <2>3, FenceOk, Isa
    <1>10. CASE ev.tag = "TaskHeartbeat"
        <2>1. Handle(ev, doc, t) = HandleTaskHeartbeat(ev, doc, t)
            BY ONLY <1>10, Z3 DEF Handle
        <2>2. QED
            BY <2>1, BeatOk, Isa
    <1>11. CASE ev.tag = "TaskSuspend"
        <2>1. Handle(ev, doc, t) = HandleTaskSuspend(ev, doc, t)
            BY ONLY <1>11, Z3 DEF Handle
        <2>2. QED
            BY <2>1, SusOk, Isa
    <1>12. CASE ev.tag = "TaskFulfill"
        <2>1. Handle(ev, doc, t) = HandleTaskFulfill(ev, doc, t)
            BY ONLY <1>12, Z3 DEF Handle
        <2>2. QED
            BY <2>1, FulOk, Isa
    <1>13. CASE ev.tag = "TaskRelease"
        <2>1. Handle(ev, doc, t) = HandleTaskRelease(ev, doc, t)
            BY ONLY <1>13, Z3 DEF Handle
        <2>2. QED
            BY <2>1, RelOk, Isa
    <1>14. CASE ev.tag = "TaskHalt"
        <2>1. Handle(ev, doc, t) = HandleTaskHalt(ev, doc, t)
            BY ONLY <1>14, Z3 DEF Handle
        <2>2. QED
            BY <2>1, HaltOk, Isa
    <1>15. CASE ev.tag = "TaskContinue"
        <2>1. Handle(ev, doc, t) = HandleTaskContinue(ev, doc, t)
            BY ONLY <1>15, Z3 DEF Handle
        <2>2. QED
            BY <2>1, ContOk, Isa
    <1>16. CASE ev.tag = "Timeout"
        <2>1. Handle(ev, doc, t) = Skip(doc)
            BY ONLY <1>16, Z3 DEF Handle
        <2>2. QED
            BY <2>1, SkipBoth, Isa
    <1>17. QED
        BY <1>2, <1>3, <1>4, <1>5, <1>7, <1>8, <1>9,
           <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, Z3
           DEF HandleTag

(* ------------------------------------------------------------------ *)

LEMMA TimeOk ==
    ASSUME NEW doc, NEW t, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(SweepTimeoutAt(doc, t).doc)
           /\ Home(SweepTimeoutAt(doc, t).doc, o)
PROOF
    <1>1. HIDE DEF SetToSeq
    <1> DEFINE S ==
            { i \in DOMAIN doc :
                doc[i].promise.state = "pending"
                /\ doc[i].promise.timeoutAt <= t }
    <1>2. CASE S = {}
        <2>1. SweepTimeoutAt(doc, t) =
                LET S  == { i \in DOMAIN doc :
                              doc[i].promise.state = "pending"
                              /\ doc[i].promise.timeoutAt <= t }
                    qp == SetToSeq(S)
                    ql == SetToSeq({ i \in S : doc[i].task.state = "acquired" })
                    qr == SetToSeq({ i \in S : doc[i].task.state = "pending" })
                IN
                IF S = {} THEN
                    [ doc |-> doc, puts |-> << >>, dels |-> << >>, sends |-> << >> ]
                ELSE
                [ doc   |-> [ i \in DOMAIN doc |->
                                IF i \in S THEN Project(doc[i], t) ELSE doc[i] ],
                  puts  |-> << >>,
                  dels  |->    [ n \in 1 .. Len(qp) |->
                                   [at |-> doc[qp[n]].promise.timeoutAt, id |-> qp[n], kind |-> "promise"] ]
                            \o [ n \in 1 .. Len(ql) |->
                                   [at |-> doc[ql[n]].task.leaseTimeoutAt,    id |-> ql[n], kind |-> "lease"] ]
                            \o [ n \in 1 .. Len(qr) |->
                                   [at |-> doc[qr[n]].task.retryTimeoutAt,      id |-> qr[n], kind |-> "retry"] ],
                  sends |-> << >> ]
            BY ONLY DEF SweepTimeoutAt
        <2>2. SweepTimeoutAt(doc, t).doc = doc
            BY <1>2, <2>1, Isa DEF S
        <2>3. DocOk(doc) /\ Home(doc, o)
            BY Z3 DEF DocOk, Home
        <2>4. QED
            BY <2>2, <2>3, Isa
    <1>3. CASE S /= {}
        <2> DEFINE img ==
                [ i \in DOMAIN doc |->
                    IF i \in S THEN Project(doc[i], t) ELSE doc[i] ]
        <2>1. SweepTimeoutAt(doc, t).doc = img
            BY ONLY <1>3, Z3 DEF SweepTimeoutAt, S, img
        <2>2. DOMAIN img = DOMAIN doc
            BY DomCtor, Isa DEF img
        <2>3. ASSUME NEW i \in DOMAIN doc
              PROVE  img[i].promise.callbacks \subseteq DOMAIN doc
                     /\ Guard(img[i])
            <3>1. img[i] = IF i \in S THEN Project(doc[i], t) ELSE doc[i]
                BY AppCtor, Isa DEF img
            <3>2. CASE i \in S
                <4>1. img[i] = Project(doc[i], t)
                    BY ONLY <3>1, <3>2, Z3
                <4>2. Project(doc[i], t).promise.callbacks
                        = doc[i].promise.callbacks
                    BY ProjCb, Z3
                <4>3. DocOk(doc) /\ i \in DOMAIN doc
                    BY Z3 DEF DocOk
                <4>4. doc[i].promise.callbacks \subseteq DOMAIN doc
                      /\ Guard(doc[i])
                    BY ONLY <4>3, Isa DEF DocOk
                <4>5. Guard(Project(doc[i], t))
                    BY <4>4, ProjGuard, Z3
                <4>6. img[i].promise.callbacks
                        = Project(doc[i], t).promise.callbacks
                      /\ (Guard(img[i]) <=> Guard(Project(doc[i], t)))
                    BY ONLY <4>1, Isa
                <4>7. QED
                    BY ONLY <4>2, <4>4, <4>5, <4>6, Z3
            <3>3. CASE i \notin S
                <4>1. img[i] = doc[i]
                    BY ONLY <3>1, <3>3, Z3
                <4>2. DocOk(doc) /\ i \in DOMAIN doc
                    BY Z3 DEF DocOk
                <4>3. doc[i].promise.callbacks \subseteq DOMAIN doc
                      /\ Guard(doc[i])
                    BY ONLY <4>2, Isa DEF DocOk
                <4>4. img[i].promise.callbacks = doc[i].promise.callbacks
                      /\ (Guard(img[i]) <=> Guard(doc[i]))
                    BY ONLY <4>1, Isa
                <4>5. QED
                    BY ONLY <4>3, <4>4, Z3
            <3>4. QED
                BY ONLY <3>2, <3>3, Z3
        <2>4. \A i \in DOMAIN img :
                img[i].promise.callbacks \subseteq DOMAIN img /\ Guard(img[i])
            BY <2>2, <2>3, Z3
        <2>5. DocOk(img)
            BY <2>4, Z3 DEF DocOk
        <2>6. Home(img, o)
            BY <2>2, SameHome, Isa
        <2>7. QED
            BY ONLY <2>1, <2>5, <2>6, Z3
    <1>4. QED
        BY ONLY <1>2, <1>3, Z3

LEMMA KeepDoc ==
    ASSUME NEW doc, NEW o, NEW got,
           DocOk(doc), Home(doc, o), got = doc
    PROVE  DocOk(got) /\ Home(got, o)
PROOF
    BY Isa

LEMMA ImgOk ==
    ASSUME NEW doc, NEW o, NEW img,
           DocOk(doc), Home(doc, o),
           DOMAIN img = DOMAIN doc,
           \A i \in DOMAIN doc :
              img[i].promise.callbacks \subseteq DOMAIN doc /\ Guard(img[i])
    PROVE  DocOk(img) /\ Home(img, o)
PROOF
    <1>1. \A i \in DOMAIN img :
            img[i].promise.callbacks \subseteq DOMAIN img /\ Guard(img[i])
        BY Z3
    <1>2. DocOk(img)
        BY <1>1, Z3 DEF DocOk
    <1>3. Home(img, o)
        BY Isa DEF Home
    <1>4. QED
        BY <1>2, <1>3, Z3

LEMMA PosTime ==
    ASSUME NEW t \in Nat
    PROVE  t /= NoTime
PROOF
    BY Z3 DEF NoTime

LEMMA DropLsBits ==
    ASSUME NEW obj
    PROVE  /\ DropListeners(obj).promise.callbacks = obj.promise.callbacks
           /\ DropListeners(obj).promise.listeners = {}
           /\ DropListeners(obj).promise.state = obj.promise.state
           /\ DropListeners(obj).task = obj.task
PROOF
    <1> DEFINE p ==
            [ state     |-> obj.promise.state,
              param     |-> obj.promise.param,
              value     |-> obj.promise.value,
              tags      |-> obj.promise.tags,
              timeoutAt |-> obj.promise.timeoutAt,
              createdAt |-> obj.promise.createdAt,
              settledAt |-> obj.promise.settledAt,
              callbacks |-> obj.promise.callbacks,
              listeners |-> {} ]
    <1> DEFINE nw == [promise |-> p, task |-> obj.task]
    <1>1. p.callbacks = obj.promise.callbacks
          /\ p.listeners = {}
          /\ p.state = obj.promise.state
        BY ONLY Z3 DEF p
    <1>2. DropListeners(obj) = nw
        BY ONLY Z3 DEF DropListeners, p, nw
    <1>3. nw.promise = p /\ nw.task = obj.task
        BY ONLY Z3 DEF nw
    <1>4. nw.promise.callbacks = p.callbacks
          /\ nw.promise.listeners = p.listeners
          /\ nw.promise.state = p.state
          /\ nw.task = obj.task
        BY ONLY Z3 DEF nw
    <1>5. QED
        BY ONLY <1>1, <1>2, <1>3, <1>4, Z3

LEMMA DropLsGuard ==
    ASSUME NEW obj, Guard(obj)
    PROVE  Guard(DropListeners(obj))
           /\ DropListeners(obj).promise.callbacks = obj.promise.callbacks
PROOF
    <1> DEFINE nw == DropListeners(obj)
    <1>1. nw.promise.callbacks = obj.promise.callbacks
          /\ nw.promise.listeners = {}
          /\ nw.promise.state = obj.promise.state
          /\ nw.task = obj.task
        BY ONLY DropLsBits DEF nw
    <1>2. nw.task.state = obj.task.state
          /\ nw.task.ttl = obj.task.ttl
          /\ nw.task.leaseTimeoutAt = obj.task.leaseTimeoutAt
          /\ nw.task.retryTimeoutAt = obj.task.retryTimeoutAt
        BY ONLY <1>1, Isa
    <1>3. {} \subseteq Address
        BY Z3
    <1>4. obj.task.state = "acquired" =>
                /\ obj.task.leaseTimeoutAt /= NoTime
                /\ obj.task.ttl \in Ttl
                /\ obj.promise.state = "pending"
          /\ obj.task.state = "pending" =>
                /\ obj.task.retryTimeoutAt /= NoTime
                /\ obj.promise.state = "pending"
          /\ obj.task.state = "suspended" => obj.promise.state = "pending"
        BY Z3 DEF Guard
    <1>5. QED
        BY <1>1, <1>2, <1>3, <1>4, Isa DEF Guard, nw

LEMMA LsOk ==
    ASSUME NEW doc, NEW t, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(SweepListeners(doc, t).doc)
           /\ Home(SweepListeners(doc, t).doc, o)
PROOF
    <1>1. HIDE DEF SetToSeq
    <1> DEFINE pairs ==
            { x \in [id : { i \in DOMAIN doc : doc[i].promise.state /= "pending" },
                     address : Address] :
                x.address \in doc[x.id].promise.listeners }
    <1>2. CASE pairs = {}
        <2>1. SweepListeners(doc, t) =
                LET pairs == { x \in [id : { i \in DOMAIN doc :
                                               doc[i].promise.state /= "pending" },
                                      address : Address] :
                                  x.address \in doc[x.id].promise.listeners }
                    q == SetToSeq(pairs)
                IN
                IF pairs = {} THEN
                    [ doc |-> doc, puts |-> << >>, dels |-> << >>, sends |-> << >> ]
                ELSE
                [ doc   |-> [ i \in DOMAIN doc |->
                                IF doc[i].promise.state /= "pending"
                                   /\ doc[i].promise.listeners /= {} THEN
                                    DropListeners(doc[i])
                                ELSE
                                    doc[i] ],
                  puts  |-> << >>,
                  dels  |-> << >>,
                  sends |-> [ n \in 1 .. Len(q) |->
                                [ address |-> q[n].address,
                                  message |-> [ tag   |-> "Unblock",
                                                id    |-> q[n].id,
                                                state |-> doc[q[n].id].promise.state ] ] ] ]
            BY ONLY DEF SweepListeners
        <2>2. SweepListeners(doc, t).doc = doc
            BY <1>2, <2>1, Isa DEF pairs
        <2>3. QED
            BY <2>2, KeepDoc, Z3
    <1>3. CASE pairs /= {}
        <2> DEFINE img ==
                [ i \in DOMAIN doc |->
                    IF doc[i].promise.state /= "pending"
                       /\ doc[i].promise.listeners /= {} THEN
                        DropListeners(doc[i])
                    ELSE
                        doc[i] ]
        <2>1. SweepListeners(doc, t).doc = img
            BY ONLY <1>3, Z3 DEF SweepListeners, pairs, img
        <2>2. DOMAIN img = DOMAIN doc
            BY DomCtor, Isa DEF img
        <2>3. ASSUME NEW i \in DOMAIN doc
              PROVE  img[i].promise.callbacks \subseteq DOMAIN doc
                     /\ Guard(img[i])
            <3> DEFINE open ==
                    doc[i].promise.state /= "pending"
                    /\ doc[i].promise.listeners /= {}
            <3>1. img[i] = IF open THEN DropListeners(doc[i]) ELSE doc[i]
                BY AppCtor, Isa DEF img, open
            <3>2. CASE open
                <4>1. img[i] = DropListeners(doc[i])
                    BY ONLY <3>1, <3>2, Z3 DEF open
                <4>2. DocOk(doc) /\ i \in DOMAIN doc
                    BY Z3 DEF DocOk
                <4>3. Guard(doc[i])
                      /\ doc[i].promise.callbacks \subseteq DOMAIN doc
                    BY ONLY <4>2, Isa DEF DocOk
                <4>4. Guard(DropListeners(doc[i]))
                      /\ DropListeners(doc[i]).promise.callbacks
                            = doc[i].promise.callbacks
                    BY <4>3, DropLsGuard, Z3
                <4>5. img[i].promise.callbacks
                        = DropListeners(doc[i]).promise.callbacks
                      /\ (Guard(img[i]) <=> Guard(DropListeners(doc[i])))
                    BY ONLY <4>1, Isa
                <4>6. QED
                    BY ONLY <4>3, <4>4, <4>5, Z3
            <3>3. CASE ~open
                <4>1. img[i] = doc[i]
                    BY ONLY <3>1, <3>3, Z3 DEF open
                <4>2. DocOk(doc) /\ i \in DOMAIN doc
                    BY Z3 DEF DocOk
                <4>3. Guard(doc[i])
                      /\ doc[i].promise.callbacks \subseteq DOMAIN doc
                    BY ONLY <4>2, Isa DEF DocOk
                <4>4. img[i].promise.callbacks = doc[i].promise.callbacks
                      /\ (Guard(img[i]) <=> Guard(doc[i]))
                    BY ONLY <4>1, Isa
                <4>5. QED
                    BY ONLY <4>3, <4>4, Z3
            <3>4. QED
                BY ONLY <3>2, <3>3, Z3
        <2>4. HIDE DEF img, pairs
        <2>5. DOMAIN img = DOMAIN doc
              /\ DocOk(doc) /\ Home(doc, o)
              /\ \A i \in DOMAIN doc :
                    img[i].promise.callbacks \subseteq DOMAIN doc
                    /\ Guard(img[i])
            BY <2>2, <2>3, Z3 DEF DocOk, Home
        <2>6. DocOk(img) /\ Home(img, o)
            BY ONLY <2>5, ImgOk, Z3
        <2>7. QED
            BY ONLY <2>1, <2>6, Z3
    <1>4. QED
        BY ONLY <1>2, <1>3, Z3

LEMMA ExpBits ==
    ASSUME NEW obj, NEW t \in Nat,
           Guard(obj), obj.task.state = "acquired"
    PROVE  LET nw == [ obj EXCEPT !.task.state          = "pending",
                                  !.task.pid            = NoPid,
                                  !.task.ttl            = NoTime,
                                  !.task.leaseTimeoutAt = NoTime,
                                  !.task.retryTimeoutAt = t ]
            IN  Guard(nw) /\ nw.promise.callbacks = obj.promise.callbacks
PROOF
    <1> DEFINE t1 == [obj.task EXCEPT !.state = "pending"]
    <1> DEFINE t2 == [t1 EXCEPT !.pid = NoPid]
    <1> DEFINE t3 == [t2 EXCEPT !.ttl = NoTime]
    <1> DEFINE t4 == [t3 EXCEPT !.leaseTimeoutAt = NoTime]
    <1> DEFINE t5 == [t4 EXCEPT !.retryTimeoutAt = t]
    <1> DEFINE raw == [obj EXCEPT !.task = t5]
    <1>1. t1.state = "pending"
          /\ t1.pid = obj.task.pid
          /\ t1.ttl = obj.task.ttl
          /\ t1.leaseTimeoutAt = obj.task.leaseTimeoutAt
          /\ t1.retryTimeoutAt = obj.task.retryTimeoutAt
        BY ONLY Z3 DEF t1
    <1>2. t2.pid = NoPid /\ t2.state = t1.state
          /\ t2.ttl = t1.ttl
          /\ t2.leaseTimeoutAt = t1.leaseTimeoutAt
          /\ t2.retryTimeoutAt = t1.retryTimeoutAt
        BY ONLY Z3 DEF t2
    <1>3. t3.ttl = NoTime /\ t3.state = t2.state
          /\ t3.pid = t2.pid
          /\ t3.leaseTimeoutAt = t2.leaseTimeoutAt
          /\ t3.retryTimeoutAt = t2.retryTimeoutAt
        BY ONLY Z3 DEF t3
    <1>4. t4.leaseTimeoutAt = NoTime /\ t4.state = t3.state
          /\ t4.pid = t3.pid /\ t4.ttl = t3.ttl
          /\ t4.retryTimeoutAt = t3.retryTimeoutAt
        BY ONLY Z3 DEF t4
    <1>5. t5.retryTimeoutAt = t /\ t5.state = t4.state
          /\ t5.pid = t4.pid /\ t5.ttl = t4.ttl
          /\ t5.leaseTimeoutAt = t4.leaseTimeoutAt
        BY ONLY Z3 DEF t5
    <1>6. t5.state = "pending" /\ t5.pid = NoPid /\ t5.ttl = NoTime
          /\ t5.leaseTimeoutAt = NoTime /\ t5.retryTimeoutAt = t
        BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5, Z3
    <1>7. raw.promise = obj.promise /\ raw.task = t5
        BY ONLY Z3 DEF raw
    <1>8. raw.promise.callbacks = obj.promise.callbacks
          /\ raw.promise.listeners = obj.promise.listeners
          /\ raw.promise.state = obj.promise.state
        BY ONLY <1>7, Isa
    <1>9. raw.task.state = t5.state
          /\ raw.task.retryTimeoutAt = t5.retryTimeoutAt
        BY ONLY <1>7, Isa
    <1>10. t /= NoTime
        BY PosTime, Z3
    <1>11. obj.promise.state = "pending"
           /\ obj.promise.listeners \subseteq Address
        BY Z3 DEF Guard
    <1>12. Guard(raw)
        BY ONLY <1>6, <1>8, <1>9, <1>10, <1>11, Z3 DEF Guard
    <1>13. raw = [ obj EXCEPT !.task.state          = "pending",
                              !.task.pid            = NoPid,
                              !.task.ttl            = NoTime,
                              !.task.leaseTimeoutAt = NoTime,
                              !.task.retryTimeoutAt = t ]
        BY Zenon DEF raw, t1, t2, t3, t4, t5
    <1>14. QED
        BY ONLY <1>8, <1>12, <1>13, Isa

LEMMA RetryBits ==
    ASSUME NEW obj, NEW t \in Nat,
           Guard(obj), obj.task.state = "pending"
    PROVE  LET nw == [ obj EXCEPT !.task.retryTimeoutAt = t + RetryTimeout ]
            IN  Guard(nw) /\ nw.promise.callbacks = obj.promise.callbacks
PROOF
    <1> DEFINE t1 == [obj.task EXCEPT !.retryTimeoutAt = t + RetryTimeout]
    <1> DEFINE raw == [obj EXCEPT !.task = t1]
    <1>1. t1.state = obj.task.state
          /\ t1.ttl = obj.task.ttl
          /\ t1.leaseTimeoutAt = obj.task.leaseTimeoutAt
          /\ t1.retryTimeoutAt = t + RetryTimeout
        BY ONLY Z3 DEF t1
    <1>2. raw.promise = obj.promise /\ raw.task = t1
        BY ONLY Z3 DEF raw
    <1>3. raw.promise.callbacks = obj.promise.callbacks
          /\ raw.promise.listeners = obj.promise.listeners
          /\ raw.promise.state = obj.promise.state
        BY ONLY <1>2, Isa
    <1>4. raw.task.state = t1.state
          /\ raw.task.retryTimeoutAt = t1.retryTimeoutAt
          /\ raw.task.ttl = t1.ttl
          /\ raw.task.leaseTimeoutAt = t1.leaseTimeoutAt
        BY ONLY <1>2, Isa
    <1>5. obj.task.state = "pending"
          /\ obj.promise.state = "pending"
          /\ obj.promise.listeners \subseteq Address
        BY Z3 DEF Guard
    <1>6. raw.task.state = "pending"
        BY ONLY <1>1, <1>4, <1>5, Z3
    <1>7. t + RetryTimeout /= NoTime
        BY RetryTime, RetryNat, Z3
    <1>8. Guard(raw)
        BY ONLY <1>1, <1>3, <1>4, <1>5, <1>6, <1>7, Z3 DEF Guard
    <1>9. raw = [ obj EXCEPT !.task.retryTimeoutAt = t + RetryTimeout ]
        BY Zenon DEF raw, t1
    <1>10. QED
        BY ONLY <1>3, <1>8, <1>9, Isa

LEMMA RetryOk ==
    ASSUME NEW doc, NEW t \in Nat, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(SweepRetryAt(doc, t).doc)
           /\ Home(SweepRetryAt(doc, t).doc, o)
PROOF
    <1>1. HIDE DEF SetToSeq
    <1> DEFINE S ==
            { i \in DOMAIN doc :
                doc[i].task.state = "pending"
                /\ doc[i].task.retryTimeoutAt <= t }
    <1>2. CASE S = {}
        <2>1. SweepRetryAt(doc, t) =
                LET S == { i \in DOMAIN doc :
                             doc[i].task.state = "pending"
                             /\ doc[i].task.retryTimeoutAt <= t }
                    q == SetToSeq(S)
                IN
                IF S = {} THEN
                    [ doc |-> doc, puts |-> << >>, dels |-> << >>, sends |-> << >> ]
                ELSE
                [ doc   |-> [ i \in DOMAIN doc |->
                                IF i \in S THEN
                                    [ doc[i] EXCEPT !.task.retryTimeoutAt = t + RetryTimeout ]
                                ELSE
                                    doc[i] ],
                  puts  |-> [ n \in 1 .. Len(q) |->
                                [at |-> t + RetryTimeout, id |-> q[n], kind |-> "retry"] ],
                  dels  |-> [ n \in 1 .. Len(q) |->
                                [at |-> doc[q[n]].task.retryTimeoutAt, id |-> q[n], kind |-> "retry"] ],
                  sends |-> [ n \in 1 .. Len(q) |->
                                [ address |-> doc[q[n]].promise.tags.target,
                                  message |-> [ tag     |-> "Execute",
                                                id      |-> q[n],
                                                version |-> doc[q[n]].task.version ] ] ] ]
            BY ONLY DEF SweepRetryAt
        <2>2. SweepRetryAt(doc, t).doc = doc
            BY <1>2, <2>1, Isa DEF S
        <2>3. QED
            BY <2>2, KeepDoc, Z3
    <1>3. CASE S /= {}
        <2> DEFINE img ==
                [ i \in DOMAIN doc |->
                    IF i \in S THEN
                        [ doc[i] EXCEPT !.task.retryTimeoutAt = t + RetryTimeout ]
                    ELSE
                        doc[i] ]
        <2>1. SweepRetryAt(doc, t).doc = img
            BY ONLY <1>3, Z3 DEF SweepRetryAt, S, img
        <2>2. DOMAIN img = DOMAIN doc
            BY DomCtor, Isa DEF img
        <2>3. ASSUME NEW i \in DOMAIN doc
              PROVE  img[i].promise.callbacks \subseteq DOMAIN doc
                     /\ Guard(img[i])
            <3>1. img[i] =
                    IF i \in S THEN
                        [ doc[i] EXCEPT !.task.retryTimeoutAt = t + RetryTimeout ]
                    ELSE
                        doc[i]
                BY AppCtor, Isa DEF img
            <3>2. CASE i \in S
                <4> DEFINE nw ==
                        [ doc[i] EXCEPT !.task.retryTimeoutAt = t + RetryTimeout ]
                <4>1. img[i] = nw
                    BY ONLY <3>1, <3>2, Z3 DEF nw
                <4>2. DocOk(doc) /\ i \in DOMAIN doc
                    BY Z3 DEF DocOk
                <4>3. Guard(doc[i]) /\ doc[i].task.state = "pending"
                      /\ doc[i].promise.callbacks \subseteq DOMAIN doc
                    <5>1. i \in DOMAIN doc
                          /\ doc[i].task.state = "pending"
                          /\ doc[i].task.retryTimeoutAt <= t
                        BY <3>2, MemComp, Isa DEF S
                    <5>2. doc[i].promise.callbacks \subseteq DOMAIN doc
                          /\ Guard(doc[i])
                        BY ONLY <4>2, Isa DEF DocOk
                    <5>3. QED
                        BY ONLY <5>1, <5>2, Z3
                <4>4. Guard(nw) /\ nw.promise.callbacks = doc[i].promise.callbacks
                    BY <4>3, RetryBits, Isa DEF nw
                <4>5. img[i].promise.callbacks = nw.promise.callbacks
                      /\ (Guard(img[i]) <=> Guard(nw))
                    BY ONLY <4>1, Isa
                <4>6. QED
                    BY ONLY <4>3, <4>4, <4>5, Z3
            <3>3. CASE i \notin S
                <4>1. img[i] = doc[i]
                    BY ONLY <3>1, <3>3, Z3
                <4>2. DocOk(doc) /\ i \in DOMAIN doc
                    BY Z3 DEF DocOk
                <4>3. Guard(doc[i])
                      /\ doc[i].promise.callbacks \subseteq DOMAIN doc
                    BY ONLY <4>2, Isa DEF DocOk
                <4>4. img[i].promise.callbacks = doc[i].promise.callbacks
                      /\ (Guard(img[i]) <=> Guard(doc[i]))
                    BY ONLY <4>1, Isa
                <4>5. QED
                    BY ONLY <4>3, <4>4, Z3
            <3>4. QED
                BY ONLY <3>2, <3>3, Z3
        <2>4. HIDE DEF img, S
        <2>5. DOMAIN img = DOMAIN doc
              /\ DocOk(doc) /\ Home(doc, o)
              /\ \A i \in DOMAIN doc :
                    img[i].promise.callbacks \subseteq DOMAIN doc
                    /\ Guard(img[i])
            BY <2>2, <2>3, Z3 DEF DocOk, Home
        <2>6. DocOk(img) /\ Home(img, o)
            BY ONLY <2>5, ImgOk, Z3
        <2>7. QED
            BY ONLY <2>1, <2>6, Z3
    <1>4. QED
        BY ONLY <1>2, <1>3, Z3

LEMMA DropCbBits ==
    ASSUME NEW obj
    PROVE  /\ DropCallbacks(obj).promise.callbacks = {}
           /\ DropCallbacks(obj).promise.listeners = obj.promise.listeners
           /\ DropCallbacks(obj).promise.state = obj.promise.state
           /\ DropCallbacks(obj).task = obj.task
PROOF
    <1> DEFINE p ==
            [ state     |-> obj.promise.state,
              param     |-> obj.promise.param,
              value     |-> obj.promise.value,
              tags      |-> obj.promise.tags,
              timeoutAt |-> obj.promise.timeoutAt,
              createdAt |-> obj.promise.createdAt,
              settledAt |-> obj.promise.settledAt,
              callbacks |-> {},
              listeners |-> obj.promise.listeners ]
    <1> DEFINE nw == [promise |-> p, task |-> obj.task]
    <1>1. p.callbacks = {}
          /\ p.listeners = obj.promise.listeners
          /\ p.state = obj.promise.state
        BY ONLY Z3 DEF p
    <1>2. DropCallbacks(obj) = nw
        BY ONLY Z3 DEF DropCallbacks, p, nw
    <1>3. nw.promise = p /\ nw.task = obj.task
        BY ONLY Z3 DEF nw
    <1>4. nw.promise.callbacks = p.callbacks
          /\ nw.promise.listeners = p.listeners
          /\ nw.promise.state = p.state
          /\ nw.task = obj.task
        BY ONLY Z3 DEF nw
    <1>5. QED
        BY ONLY <1>1, <1>2, <1>3, <1>4, Z3

LEMMA DropCbGuard ==
    ASSUME NEW obj, Guard(obj)
    PROVE  Guard(DropCallbacks(obj))
           /\ DropCallbacks(obj).promise.callbacks = {}
PROOF
    <1> DEFINE nw == DropCallbacks(obj)
    <1>1. nw.promise.callbacks = {}
          /\ nw.promise.listeners = obj.promise.listeners
          /\ nw.promise.state = obj.promise.state
          /\ nw.task = obj.task
        BY ONLY DropCbBits DEF nw
    <1>2. nw.task.state = obj.task.state
          /\ nw.task.ttl = obj.task.ttl
          /\ nw.task.leaseTimeoutAt = obj.task.leaseTimeoutAt
          /\ nw.task.retryTimeoutAt = obj.task.retryTimeoutAt
        BY ONLY <1>1, Isa
    <1>3. {} \subseteq {}
        BY Z3
    <1>4. obj.promise.listeners \subseteq Address
          /\ obj.task.state = "acquired" =>
                /\ obj.task.leaseTimeoutAt /= NoTime
                /\ obj.task.ttl \in Ttl
                /\ obj.promise.state = "pending"
          /\ obj.task.state = "pending" =>
                /\ obj.task.retryTimeoutAt /= NoTime
                /\ obj.promise.state = "pending"
          /\ obj.task.state = "suspended" => obj.promise.state = "pending"
        BY Z3 DEF Guard
    <1>5. QED
        BY <1>1, <1>2, <1>4, Isa DEF Guard, nw

LEMMA WakeBits ==
    ASSUME NEW obj, NEW src, NEW t
    PROVE  /\ Wake(obj, src, t).promise = obj.promise
           /\ Wake(obj, src, t).task.state = "pending"
           /\ Wake(obj, src, t).task.retryTimeoutAt = t
PROOF
    <1> DEFINE tk ==
            [ state          |-> "pending",
              version        |-> obj.task.version,
              ttl            |-> NoTime,
              pid            |-> NoPid,
              leaseTimeoutAt |-> NoTime,
              retryTimeoutAt |-> t,
              resumes        |-> src ]
    <1> DEFINE nw == [promise |-> obj.promise, task |-> tk]
    <1>1. tk.state = "pending" /\ tk.retryTimeoutAt = t
        BY ONLY Z3 DEF tk
    <1>2. Wake(obj, src, t) = nw
        BY ONLY Z3 DEF Wake, tk, nw
    <1>3. nw.promise = obj.promise /\ nw.task = tk
        BY ONLY Z3 DEF nw
    <1>4. nw.task.state = tk.state
          /\ nw.task.retryTimeoutAt = tk.retryTimeoutAt
        BY ONLY Z3 DEF nw
    <1>5. QED
        BY ONLY <1>1, <1>2, <1>3, <1>4, Z3

LEMMA WakeGuard ==
    ASSUME NEW obj, NEW src, NEW t \in Nat,
           Guard(obj), obj.task.state = "suspended"
    PROVE  Guard(Wake(obj, src, t))
           /\ Wake(obj, src, t).promise.callbacks = obj.promise.callbacks
PROOF
    <1> DEFINE nw == Wake(obj, src, t)
    <1>1. nw.promise = obj.promise
          /\ nw.task.state = "pending"
          /\ nw.task.retryTimeoutAt = t
        BY ONLY WakeBits DEF nw
    <1>2. nw.promise.callbacks = obj.promise.callbacks
          /\ nw.promise.listeners = obj.promise.listeners
          /\ nw.promise.state = obj.promise.state
        BY ONLY <1>1, Isa
    <1>3. t /= NoTime
        BY PosTime, Z3
    <1>4. obj.promise.state = "pending"
          /\ obj.promise.listeners \subseteq Address
        BY Z3 DEF Guard
    <1>5. QED
        BY <1>1, <1>2, <1>3, <1>4, Isa DEF Guard, nw

LEMMA AddResBits ==
    ASSUME NEW obj, NEW R
    PROVE  /\ AddResumes(obj, R).promise = obj.promise
           /\ AddResumes(obj, R).task.state = obj.task.state
           /\ AddResumes(obj, R).task.ttl = obj.task.ttl
           /\ AddResumes(obj, R).task.leaseTimeoutAt = obj.task.leaseTimeoutAt
           /\ AddResumes(obj, R).task.retryTimeoutAt = obj.task.retryTimeoutAt
PROOF
    <1> DEFINE tk ==
            [ state          |-> obj.task.state,
              version        |-> obj.task.version,
              ttl            |-> obj.task.ttl,
              pid            |-> obj.task.pid,
              leaseTimeoutAt |-> obj.task.leaseTimeoutAt,
              retryTimeoutAt |-> obj.task.retryTimeoutAt,
              resumes        |-> obj.task.resumes \cup R ]
    <1> DEFINE nw == [promise |-> obj.promise, task |-> tk]
    <1>1. tk.state = obj.task.state
          /\ tk.ttl = obj.task.ttl
          /\ tk.leaseTimeoutAt = obj.task.leaseTimeoutAt
          /\ tk.retryTimeoutAt = obj.task.retryTimeoutAt
        BY ONLY Z3 DEF tk
    <1>2. AddResumes(obj, R) = nw
        BY ONLY Z3 DEF AddResumes, tk, nw
    <1>3. nw.promise = obj.promise /\ nw.task = tk
        BY ONLY Z3 DEF nw
    <1>4. nw.task.state = tk.state
          /\ nw.task.ttl = tk.ttl
          /\ nw.task.leaseTimeoutAt = tk.leaseTimeoutAt
          /\ nw.task.retryTimeoutAt = tk.retryTimeoutAt
        BY ONLY Z3 DEF nw
    <1>5. QED
        BY ONLY <1>1, <1>2, <1>3, <1>4, Z3

LEMMA AddResGuard ==
    ASSUME NEW obj, NEW R, Guard(obj)
    PROVE  Guard(AddResumes(obj, R))
           /\ AddResumes(obj, R).promise.callbacks = obj.promise.callbacks
PROOF
    <1> DEFINE nw == AddResumes(obj, R)
    <1>1. nw.promise = obj.promise
          /\ nw.task.state = obj.task.state
          /\ nw.task.ttl = obj.task.ttl
          /\ nw.task.leaseTimeoutAt = obj.task.leaseTimeoutAt
          /\ nw.task.retryTimeoutAt = obj.task.retryTimeoutAt
        BY ONLY AddResBits DEF nw
    <1>2. nw.promise.callbacks = obj.promise.callbacks
          /\ nw.promise.listeners = obj.promise.listeners
          /\ nw.promise.state = obj.promise.state
        BY ONLY <1>1, Isa
    <1>3. obj.promise.listeners \subseteq Address
          /\ obj.task.state = "acquired" =>
                /\ obj.task.leaseTimeoutAt /= NoTime
                /\ obj.task.ttl \in Ttl
                /\ obj.promise.state = "pending"
          /\ obj.task.state = "pending" =>
                /\ obj.task.retryTimeoutAt /= NoTime
                /\ obj.promise.state = "pending"
          /\ obj.task.state = "suspended" => obj.promise.state = "pending"
        BY Z3 DEF Guard
    <1>4. QED
        BY <1>1, <1>2, <1>3, Isa DEF Guard, nw

LEMMA CbOk ==
    ASSUME NEW doc, NEW t \in Nat, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(SweepCallbacks(doc, t).doc)
           /\ Home(SweepCallbacks(doc, t).doc, o)
PROOF
    <1>1. HIDE DEF SetToSeq
    <1> DEFINE S ==
            { x \in [id : { i \in DOMAIN doc : doc[i].promise.state /= "pending" },
                     awaiter : Id] :
                x.awaiter \in doc[x.id].promise.callbacks }
    <1> DEFINE Resumes(w) == { x.id : x \in { y \in S : y.awaiter = w } }
    <1> DEFINE Woken == { x.awaiter : x \in S } \cap DOMAIN doc
    <1>2. CASE S = {}
        <2>1. SweepCallbacks(doc, t) =
                LET S == { x \in [id : { i \in DOMAIN doc :
                                           doc[i].promise.state /= "pending" },
                                  awaiter : Id] :
                              x.awaiter \in doc[x.id].promise.callbacks }
                    Resumes(w) == { x.id : x \in { y \in S : y.awaiter = w } }
                    Woken == { x.awaiter : x \in S } \cap DOMAIN doc
                    q == SetToSeq({ w \in Woken :
                                      doc[w].task.state = "suspended" })
                IN
                IF S = {} THEN
                    [ doc |-> doc, puts |-> << >>, dels |-> << >>, sends |-> << >> ]
                ELSE
                [ doc   |-> [ i \in DOMAIN doc |->
                                LET struck == IF doc[i].promise.state /= "pending"
                                                 /\ doc[i].promise.callbacks /= {} THEN
                                                  DropCallbacks(doc[i])
                                              ELSE
                                                  doc[i]
                                IN
                                    IF i \notin Woken
                                       \/ struck.task.state \in {"none", "fulfilled"} THEN
                                        struck
                                    ELSE IF struck.task.state = "suspended" THEN
                                        Wake(struck, Resumes(i), t)
                                    ELSE
                                        AddResumes(struck, Resumes(i)) ],
                  puts  |-> [ n \in 1 .. Len(q) |->
                                [at |-> t, id |-> q[n], kind |-> "retry"] ],
                  dels  |-> << >>,
                  sends |-> << >> ]
            BY ONLY DEF SweepCallbacks
        <2>2. SweepCallbacks(doc, t).doc = doc
            BY <1>2, <2>1, Isa DEF S
        <2>3. QED
            BY <2>2, KeepDoc, Z3
    <1>3. CASE S /= {}
        <2> DEFINE img ==
                [ i \in DOMAIN doc |->
                    LET struck == IF doc[i].promise.state /= "pending"
                                     /\ doc[i].promise.callbacks /= {} THEN
                                      DropCallbacks(doc[i])
                                  ELSE
                                      doc[i]
                    IN
                        IF i \notin Woken
                           \/ struck.task.state \in {"none", "fulfilled"} THEN
                            struck
                        ELSE IF struck.task.state = "suspended" THEN
                            Wake(struck, Resumes(i), t)
                        ELSE
                            AddResumes(struck, Resumes(i)) ]
        <2>1. SweepCallbacks(doc, t).doc = img
            BY ONLY <1>3, Z3 DEF SweepCallbacks, S, Resumes, Woken, img
        <2>2. DOMAIN img = DOMAIN doc
            BY DomCtor, Isa DEF img
        <2>3. ASSUME NEW i \in DOMAIN doc
              PROVE  img[i].promise.callbacks \subseteq DOMAIN doc
                     /\ Guard(img[i])
            <3> DEFINE drop ==
                    doc[i].promise.state /= "pending"
                    /\ doc[i].promise.callbacks /= {}
            <3> DEFINE struck ==
                    IF drop THEN DropCallbacks(doc[i]) ELSE doc[i]
            <3> DEFINE hold ==
                    i \notin Woken \/ struck.task.state \in {"none", "fulfilled"}
            <3> DEFINE sus == struck.task.state = "suspended"
            <3>1. img[i] =
                    IF hold THEN struck
                    ELSE IF sus THEN Wake(struck, Resumes(i), t)
                    ELSE AddResumes(struck, Resumes(i))
                BY AppCtor, Isa DEF img, drop, struck, hold, sus, Woken, Resumes
            <3>2. Guard(struck)
                  /\ struck.promise.callbacks \subseteq DOMAIN doc
                <4>1. CASE drop
                    <5>1. struck = DropCallbacks(doc[i])
                        BY ONLY <4>1, Z3 DEF struck, drop
                    <5>2. DocOk(doc) /\ i \in DOMAIN doc
                        BY Z3 DEF DocOk
                    <5>3. Guard(doc[i])
                        BY ONLY <5>2, Isa DEF DocOk
                    <5>4. Guard(DropCallbacks(doc[i]))
                          /\ DropCallbacks(doc[i]).promise.callbacks = {}
                        BY <5>3, DropCbGuard, Z3
                    <5>5. {} \subseteq DOMAIN doc
                        BY Z3
                    <5>6. (Guard(struck) <=> Guard(DropCallbacks(doc[i])))
                          /\ struck.promise.callbacks
                                = DropCallbacks(doc[i]).promise.callbacks
                        BY ONLY <5>1, Isa
                    <5>7. QED
                        BY ONLY <5>4, <5>5, <5>6, Z3
                <4>2. CASE ~drop
                    <5>1. struck = doc[i]
                        BY ONLY <4>2, Z3 DEF struck, drop
                    <5>2. DocOk(doc) /\ i \in DOMAIN doc
                        BY Z3 DEF DocOk
                    <5>3. Guard(doc[i])
                          /\ doc[i].promise.callbacks \subseteq DOMAIN doc
                        BY ONLY <5>2, Isa DEF DocOk
                    <5>4. (Guard(struck) <=> Guard(doc[i]))
                          /\ struck.promise.callbacks = doc[i].promise.callbacks
                        BY ONLY <5>1, Isa
                    <5>5. QED
                        BY ONLY <5>3, <5>4, Z3
                <4>3. QED
                    BY ONLY <4>1, <4>2, Z3
            <3>3. CASE hold
                <4>1. img[i] = struck
                    BY ONLY <3>1, <3>3, Z3 DEF hold
                <4>2. (Guard(img[i]) <=> Guard(struck))
                      /\ img[i].promise.callbacks = struck.promise.callbacks
                    BY ONLY <4>1, Isa
                <4>3. HIDE DEF img
                <4>4. QED
                    BY ONLY <3>2, <4>2, Z3
            <3>4. CASE ~hold /\ sus
                <4>1. img[i] = Wake(struck, Resumes(i), t)
                    BY ONLY <3>1, <3>4, Z3 DEF hold, sus
                <4>2. struck.task.state = "suspended"
                    BY ONLY <3>4, Z3 DEF sus
                <4>3. Guard(Wake(struck, Resumes(i), t))
                      /\ Wake(struck, Resumes(i), t).promise.callbacks
                            = struck.promise.callbacks
                    BY <3>2, <4>2, WakeGuard, Z3
                <4>4. (Guard(img[i]) <=> Guard(Wake(struck, Resumes(i), t)))
                      /\ img[i].promise.callbacks
                            = Wake(struck, Resumes(i), t).promise.callbacks
                    BY ONLY <4>1, Isa
                <4>5. HIDE DEF img, Wake, Resumes
                <4>6. Wake(struck, Resumes(i), t).promise.callbacks \subseteq DOMAIN doc
                      /\ Guard(Wake(struck, Resumes(i), t))
                    BY ONLY <3>2, <4>3, Z3
                <4>7. QED
                    BY ONLY <4>4, <4>6, Z3
            <3>5. CASE ~hold /\ ~sus
                <4>1. img[i] = AddResumes(struck, Resumes(i))
                    BY ONLY <3>1, <3>5, Z3 DEF hold, sus
                <4>2. Guard(AddResumes(struck, Resumes(i)))
                      /\ AddResumes(struck, Resumes(i)).promise.callbacks
                            = struck.promise.callbacks
                    BY <3>2, AddResGuard, Z3
                <4>3. (Guard(img[i]) <=> Guard(AddResumes(struck, Resumes(i))))
                      /\ img[i].promise.callbacks
                            = AddResumes(struck, Resumes(i)).promise.callbacks
                    BY ONLY <4>1, Isa
                <4>4. HIDE DEF img, AddResumes, Resumes
                <4>5. AddResumes(struck, Resumes(i)).promise.callbacks \subseteq DOMAIN doc
                      /\ Guard(AddResumes(struck, Resumes(i)))
                    BY ONLY <3>2, <4>2, Z3
                <4>6. QED
                    BY ONLY <4>3, <4>5, Z3
            <3>6. HIDE DEF img
            <3>7. hold \/ (~hold /\ sus) \/ (~hold /\ ~sus)
                BY Z3 DEF hold, sus
            <3>8. QED
                BY ONLY <3>3, <3>4, <3>5, <3>7, Z3
        <2>4. HIDE DEF img, S, Resumes, Woken
        <2>5. DOMAIN img = DOMAIN doc
              /\ DocOk(doc) /\ Home(doc, o)
              /\ \A i \in DOMAIN doc :
                    img[i].promise.callbacks \subseteq DOMAIN doc
                    /\ Guard(img[i])
            BY <2>2, <2>3, Z3 DEF DocOk, Home
        <2>6. DocOk(img) /\ Home(img, o)
            BY ONLY <2>5, ImgOk, Z3
        <2>7. QED
            BY ONLY <2>1, <2>6, Z3
    <1>4. QED
        BY ONLY <1>2, <1>3, Z3

(* The document of an IF of two records is the IF of their documents.
   The fields stay abstract, so the five-field lease update never
   enters this proof. *)
LEMMA LetDoc ==
    ASSUME NEW U, NEW qt, NEW a, NEW b,
           NEW p1, NEW d1, NEW s1, NEW p2, NEW d2, NEW s2, NEW r,
           r = LET S == U
                   q == qt
               IN IF S = {} THEN [ doc |-> a, puts |-> p1, dels |-> d1, sends |-> s1 ]
                  ELSE [ doc |-> b, puts |-> p2, dels |-> d2, sends |-> s2 ]
    PROVE  r.doc = LET S == U
                       q == qt
                   IN IF S = {} THEN a ELSE b
PROOF
    <1>1. CASE U = {}
        BY <1>1, Z3
    <1>2. CASE U /= {}
        BY <1>2, Z3
    <1>3. QED
        BY <1>1, <1>2, Z3

(* Once the set is nonempty, the document of that same IF is the else
   document. The else document stays a parameter, so a caller can hide
   the lease record before this lemma is used. *)
LEMMA IfDoc ==
    ASSUME NEW U, NEW qt, NEW a, NEW b,
           NEW p1, NEW d1, NEW s1, NEW p2, NEW d2, NEW s2, NEW r,
           r = LET S == U
                   q == qt
               IN IF S = {} THEN [ doc |-> a, puts |-> p1, dels |-> d1, sends |-> s1 ]
                  ELSE [ doc |-> b, puts |-> p2, dels |-> d2, sends |-> s2 ],
           U /= {}
    PROVE  r.doc = b
PROOF
    <1>1. r.doc = LET S == U
                      q == qt
                  IN IF S = {} THEN a ELSE b
        BY LetDoc
    <1>2. QED
        BY <1>1, Z3

LEMMA ExpOk ==
    ASSUME NEW doc, NEW t \in Nat, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(SweepExpiresAt(doc, t).doc)
           /\ Home(SweepExpiresAt(doc, t).doc, o)
PROOF
    <1>1. HIDE DEF SetToSeq
    <1> DEFINE S ==
            { i \in DOMAIN doc :
                doc[i].task.state = "acquired"
                /\ doc[i].task.leaseTimeoutAt <= t }
    <1>2. CASE S = {}
        <2>1. SweepExpiresAt(doc, t) =
                LET S == { i \in DOMAIN doc :
                             doc[i].task.state = "acquired"
                             /\ doc[i].task.leaseTimeoutAt <= t }
                    q == SetToSeq(S)
                IN
                IF S = {} THEN
                    [ doc |-> doc, puts |-> << >>, dels |-> << >>, sends |-> << >> ]
                ELSE
                [ doc   |-> [ i \in DOMAIN doc |->
                                IF i \in S THEN
                                    [ doc[i] EXCEPT !.task.state          = "pending",
                                                    !.task.pid            = NoPid,
                                                    !.task.ttl            = NoTime,
                                                    !.task.leaseTimeoutAt = NoTime,
                                                    !.task.retryTimeoutAt = t ]
                                ELSE
                                    doc[i] ],
                  puts  |-> [ n \in 1 .. Len(q) |->
                                [at |-> t, id |-> q[n], kind |-> "retry"] ],
                  dels  |-> [ n \in 1 .. Len(q) |->
                                [at |-> doc[q[n]].task.leaseTimeoutAt,
                                 id |-> q[n], kind |-> "lease"] ],
                  sends |-> << >> ]
            BY ONLY DEF SweepExpiresAt
        <2>2. SweepExpiresAt(doc, t).doc = doc
            BY <1>2, <2>1, Isa DEF S
        <2>3. QED
            BY <2>2, KeepDoc, Z3
    <1>3. CASE S /= {}
        <2> DEFINE flat ==
                [ i \in DOMAIN doc |->
                    IF i \in S THEN
                        [ doc[i] EXCEPT !.task.state          = "pending",
                                        !.task.pid            = NoPid,
                                        !.task.ttl            = NoTime,
                                        !.task.leaseTimeoutAt = NoTime,
                                        !.task.retryTimeoutAt = t ]
                    ELSE
                        doc[i] ]
        <2>1. SweepExpiresAt(doc, t).doc = flat
            <3>1. SweepExpiresAt(doc, t) =
                    LET S == { i \in DOMAIN doc :
                                 doc[i].task.state = "acquired"
                                 /\ doc[i].task.leaseTimeoutAt <= t }
                        q == SetToSeq(S)
                    IN
                    IF S = {} THEN
                        [ doc |-> doc, puts |-> << >>, dels |-> << >>, sends |-> << >> ]
                    ELSE
                    [ doc   |-> flat,
                      puts  |-> [ n \in 1 .. Len(q) |->
                                    [at |-> t, id |-> q[n], kind |-> "retry"] ],
                      dels  |-> [ n \in 1 .. Len(q) |->
                                    [at |-> doc[q[n]].task.leaseTimeoutAt,
                                     id |-> q[n], kind |-> "lease"] ],
                      sends |-> << >> ]
                BY ONLY DEF SweepExpiresAt, flat
            <3>2. HIDE DEF flat
            <3>3. S = { i \in DOMAIN doc :
                          doc[i].task.state = "acquired"
                          /\ doc[i].task.leaseTimeoutAt <= t }
                BY ONLY DEF S
            <3>4. QED
                BY <1>3, <3>1, <3>3, IfDoc, Z3
        <2>2. DOMAIN flat = DOMAIN doc
            BY DomCtor, Isa DEF flat
        <2>3. ASSUME NEW i \in DOMAIN doc
              PROVE  flat[i].promise.callbacks \subseteq DOMAIN doc
                     /\ Guard(flat[i])
            <3>1. flat[i] =
                    IF i \in S THEN
                        [ doc[i] EXCEPT !.task.state          = "pending",
                                        !.task.pid            = NoPid,
                                        !.task.ttl            = NoTime,
                                        !.task.leaseTimeoutAt = NoTime,
                                        !.task.retryTimeoutAt = t ]
                    ELSE
                        doc[i]
                BY AppCtor, Isa DEF flat
            <3>2. CASE i \in S
                <4> DEFINE nw ==
                        [ doc[i] EXCEPT !.task.state          = "pending",
                                        !.task.pid            = NoPid,
                                        !.task.ttl            = NoTime,
                                        !.task.leaseTimeoutAt = NoTime,
                                        !.task.retryTimeoutAt = t ]
                <4>1. flat[i] = nw
                    BY ONLY <3>1, <3>2, Z3 DEF nw
                <4>2. DocOk(doc) /\ i \in DOMAIN doc
                    BY Z3 DEF DocOk
                <4>3. Guard(doc[i]) /\ doc[i].task.state = "acquired"
                      /\ doc[i].promise.callbacks \subseteq DOMAIN doc
                    <5>1. i \in DOMAIN doc
                          /\ doc[i].task.state = "acquired"
                          /\ doc[i].task.leaseTimeoutAt <= t
                        BY <3>2, MemComp, Isa DEF S
                    <5>2. doc[i].promise.callbacks \subseteq DOMAIN doc
                          /\ Guard(doc[i])
                        BY ONLY <4>2, Isa DEF DocOk
                    <5>3. QED
                        BY ONLY <5>1, <5>2, Z3
                <4>4. Guard(nw) /\ nw.promise.callbacks = doc[i].promise.callbacks
                    BY <4>3, ExpBits, Isa DEF nw
                <4>5. flat[i].promise.callbacks = nw.promise.callbacks
                      /\ (Guard(flat[i]) <=> Guard(nw))
                    BY ONLY <4>1, Isa
                <4>6. QED
                    BY ONLY <4>3, <4>4, <4>5, Z3
            <3>3. CASE i \notin S
                <4>1. flat[i] = doc[i]
                    BY ONLY <3>1, <3>3, Z3
                <4>2. DocOk(doc) /\ i \in DOMAIN doc
                    BY Z3 DEF DocOk
                <4>3. Guard(doc[i])
                      /\ doc[i].promise.callbacks \subseteq DOMAIN doc
                    BY ONLY <4>2, Isa DEF DocOk
                <4>4. flat[i].promise.callbacks = doc[i].promise.callbacks
                      /\ (Guard(flat[i]) <=> Guard(doc[i]))
                    BY ONLY <4>1, Isa
                <4>5. QED
                    BY ONLY <4>3, <4>4, Z3
            <3>4. QED
                BY ONLY <3>2, <3>3, Z3
        <2>4. HIDE DEF flat, S
        <2>5. DOMAIN flat = DOMAIN doc
              /\ DocOk(doc) /\ Home(doc, o)
              /\ \A i \in DOMAIN doc :
                    flat[i].promise.callbacks \subseteq DOMAIN doc
                    /\ Guard(flat[i])
            BY <2>2, <2>3, Z3 DEF DocOk, Home
        <2>6. DocOk(flat) /\ Home(flat, o)
            BY ONLY <2>5, ImgOk, Z3
        <2>7. QED
            BY ONLY <2>1, <2>6, Z3
    <1>4. QED
        BY ONLY <1>2, <1>3, Z3

LEMMA MergeDoc ==
    ASSUME NEW a, NEW b
    PROVE  Merge(a, b).doc = b.doc
PROOF
    BY ONLY Z3 DEF Merge

LEMMA SweepOk ==
    ASSUME NEW doc, NEW t \in Nat, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(Sweep(doc, t).doc)
           /\ Home(Sweep(doc, t).doc, o)
PROOF
    <1> DEFINE s1 == SweepTimeoutAt(doc, t)
    <1> DEFINE s2 == Merge(s1, SweepListeners(s1.doc, t))
    <1> DEFINE s3 == Merge(s2, SweepCallbacks(s2.doc, t))
    <1> DEFINE s4 == Merge(s3, SweepExpiresAt(s3.doc, t))
    <1>1. Sweep(doc, t) = Merge(s4, SweepRetryAt(s4.doc, t))
        BY ONLY Z3 DEF Sweep, s1, s2, s3, s4
    <1>2. DocOk(s1.doc) /\ Home(s1.doc, o)
        BY TimeOk, Z3
    <1>3. s2.doc = SweepListeners(s1.doc, t).doc
        BY ONLY MergeDoc DEF s2
    <1>4. DocOk(SweepListeners(s1.doc, t).doc)
          /\ Home(SweepListeners(s1.doc, t).doc, o)
        BY <1>2, LsOk, Z3
    <1>5. DocOk(s2.doc) /\ Home(s2.doc, o)
        BY ONLY <1>3, <1>4, Z3
    <1>6. s3.doc = SweepCallbacks(s2.doc, t).doc
        BY ONLY MergeDoc DEF s3
    <1>7. DocOk(SweepCallbacks(s2.doc, t).doc)
          /\ Home(SweepCallbacks(s2.doc, t).doc, o)
        BY <1>5, CbOk, Z3
    <1>8. DocOk(s3.doc) /\ Home(s3.doc, o)
        BY ONLY <1>6, <1>7, Z3
    <1>9. s4.doc = SweepExpiresAt(s3.doc, t).doc
        BY ONLY MergeDoc DEF s4
    <1>10. DocOk(SweepExpiresAt(s3.doc, t).doc)
           /\ Home(SweepExpiresAt(s3.doc, t).doc, o)
        BY <1>8, ExpOk, Z3
    <1>11. DocOk(s4.doc) /\ Home(s4.doc, o)
        BY ONLY <1>9, <1>10, Z3
    <1>12. Sweep(doc, t).doc = SweepRetryAt(s4.doc, t).doc
        BY ONLY <1>1, MergeDoc, Z3
    <1>13. DocOk(SweepRetryAt(s4.doc, t).doc)
           /\ Home(SweepRetryAt(s4.doc, t).doc, o)
        BY <1>11, RetryOk, Z3
    <1>14. HIDE DEF Sweep, s1, s2, s3, s4
    <1>15. QED
        BY ONLY <1>12, <1>13, Z3

LEMMA EmptyDoc ==
    ASSUME NEW o
    PROVE  DocOk(EmptyFn) /\ Home(EmptyFn, o)
PROOF
    <1>1. EmptyFn = << >>
        BY DEF EmptyFn
    <1>2. << >> \in Seq(Nat) /\ Len(<< >>) = 0
        BY EmptySeq, Z3
    <1>3. DOMAIN << >> = 1 .. Len(<< >>)
        BY <1>2, LenProperties, Z3
    <1>4. DOMAIN EmptyFn = {}
        BY <1>1, <1>2, <1>3, Z3
    <1>5. QED
        BY <1>4, Z3 DEF DocOk, Home

LEMMA PlacedInit ==
    ASSUME Init
    PROVE  Placed
PROOF
    <1>1. docs = [o \in Origin |-> EmptyFn]
        BY DEF Init
    <1>2. DOMAIN docs = Origin
        BY <1>1, DomCtor, Isa
    <1>3. ASSUME NEW o \in Origin
          PROVE  DocOk(docs[o]) /\ Home(docs[o], o)
        <2>1. docs[o] = EmptyFn
            BY <1>1, <1>3, AppCtor, Isa
        <2>2. QED
            BY <2>1, EmptyDoc, Z3
    <1>4. QED
        BY <1>2, <1>3, Z3 DEF Placed

LEMMA PlaceStay ==
    ASSUME Placed, docs' = docs
    PROVE  Placed'
PROOF
    BY Isa DEF Placed

LEMMA ExceptOne ==
    ASSUME NEW f, NEW k \in DOMAIN f, NEW v, NEW g,
           g = [f EXCEPT ![k] = v]
    PROVE  DOMAIN g = DOMAIN f /\ g[k] = v
           /\ \A q \in DOMAIN f : q # k => g[q] = f[q]
PROOF
    <1>1. g = [f EXCEPT ![k] = v]
        BY Z3
    <1>2. DOMAIN g = DOMAIN f /\ g[k] = v
        BY ONLY <1>1, Z3
    <1>3. ASSUME NEW q \in DOMAIN f, q # k
          PROVE  g[q] = f[q]
        BY ONLY <1>1, <1>3, Z3
    <1>4. QED
        BY <1>2, <1>3, Z3

LEMMA ReplaceDoc ==
    ASSUME Placed,
           NEW o \in Origin, NEW body,
           DocOk(body), Home(body, o),
           docs' = [docs EXCEPT ![o] = body]
    PROVE  Placed'
PROOF
    <1>1. DOMAIN docs = Origin
        BY Z3 DEF Placed
    <1>2. o \in DOMAIN docs
        BY <1>1, Z3
    <1>3. DOMAIN docs' = DOMAIN docs /\ docs'[o] = body
          /\ \A q \in DOMAIN docs : q # o => docs'[q] = docs[q]
        BY <1>2, ExceptOne, Z3
    <1>4. DOMAIN docs' = Origin
        BY <1>1, <1>3, Z3
    <1>5. ASSUME NEW q \in Origin
          PROVE  DocOk(docs'[q]) /\ Home(docs'[q], q)
        <2>1. CASE q = o
            BY <1>3, <1>5, <2>1, Z3
        <2>2. CASE q # o
            <3>1. docs'[q] = docs[q]
                BY <1>1, <1>3, <1>5, <2>2, Z3
            <3>2. DocOk(docs[q]) /\ Home(docs[q], q)
                BY <1>5, Z3 DEF Placed
            <3>3. QED
                BY <3>1, <3>2, Z3
        <2>3. QED
            BY <2>1, <2>2, Z3
    <1>6. QED
        BY <1>4, <1>5, Z3 DEF Placed

LEMMA SweptHandle ==
    ASSUME NEW doc, NEW ev, NEW t \in Nat, NEW o,
           DocOk(doc), Home(doc, o),
           ev \in Event, ev.tag \in HandleTag, OriginOf(ev) = o
    PROVE  DocOk(Handle(ev, Sweep(doc, t).doc, t).doc)
           /\ Home(Handle(ev, Sweep(doc, t).doc, t).doc, o)
PROOF
    <1>1. DocOk(Sweep(doc, t).doc) /\ Home(Sweep(doc, t).doc, o)
        BY SweepOk, Z3
    <1>2. QED
        BY <1>1, HandleOk, Z3

LEMMA PutWrite ==
    ASSUME NEW r \in DOMAIN steps, PerformPut(r),
           NEW e, NEW o,
           e = Head(steps[r].pending),
           o = OriginOf(steps[r].ev)
    PROVE  docs' = [docs EXCEPT ![o] = e.body]
           /\ docs[o] = steps[r].expect
           /\ now' = now
           /\ e.tag = "PutDocument"
PROOF
    BY Z3 DEF PerformPut

LEMMA PutKeeps ==
    ASSUME Placed, now \in Nat,
           NEW r \in DOMAIN steps, PerformPut(r),
           steps[r].at \in 0 .. now,
           steps[r].ev \in Event,
           steps[r].ev.tag \in HandleTag,
           NEW e, NEW o,
           e = Head(steps[r].pending),
           o = OriginOf(steps[r].ev),
           o \in Origin,
           e.body = Handle(steps[r].ev,
                           Sweep(steps[r].expect, steps[r].at).doc,
                           steps[r].at).doc
    PROVE  Placed'
PROOF
    <1>1. docs' = [docs EXCEPT ![o] = e.body]
          /\ docs[o] = steps[r].expect
        BY PutWrite, Z3
    <1>2. steps[r].at \in Nat
        BY AtNat, Z3
    <1>3. DocOk(docs[o]) /\ Home(docs[o], o)
        BY Z3 DEF Placed
    <1>4. DocOk(steps[r].expect) /\ Home(steps[r].expect, o)
        BY <1>1, <1>3, Z3
    <1>5. DocOk(e.body) /\ Home(e.body, o)
        BY <1>2, <1>4, SweptHandle, Z3
    <1>6. HIDE DEF Sweep, Handle, PerformPut
    <1>7. docs' = [docs EXCEPT ![o] = e.body]
        BY ONLY <1>1, Z3
    <1>8. Placed /\ o \in Origin /\ DocOk(e.body) /\ Home(e.body, o)
        BY <1>5, Z3
    <1>9. QED
        BY ONLY <1>7, <1>8, ReplaceDoc, Isa

(* A step that does not land a document leaves every origin document
   where it is, so the placement invariant is unchanged. *)
LEMMA DocStay ==
    ASSUME Next,
           \A r \in DOMAIN steps : ~PerformPut(r)
    PROVE  docs' = docs
PROOF
    <1>1. ASSUME NEW ev \in ExternalEvent, SubmitExternal(ev)
          PROVE  docs' = docs
        BY <1>1, Z3 DEF SubmitExternal
    <1>2. ASSUME NEW name \in DOMAIN timeouts, SubmitInternal(name)
          PROVE  docs' = docs
        BY <1>2, Z3 DEF SubmitInternal
    <1>3. ASSUME NEW r \in DOMAIN steps, Process(r)
          PROVE  docs' = docs
        BY <1>3, Isa DEF Process
    <1>4. ASSUME NEW r \in DOMAIN steps, Crash(r)
          PROVE  docs' = docs
        BY <1>4, Z3 DEF Crash
    <1>5. ASSUME Clock
          PROVE  docs' = docs
        BY <1>5, Z3 DEF Clock
    <1>6. ASSUME NEW r \in DOMAIN steps, PerformDone(r)
          PROVE  docs' = docs
        BY <1>6, Z3 DEF PerformDone
    <1>7. ASSUME NEW r \in DOMAIN steps, PerformPutTimeout(r)
          PROVE  docs' = docs
        BY <1>7, Z3 DEF PerformPutTimeout
    <1>8. ASSUME NEW r \in DOMAIN steps, PerformDelTimeout(r)
          PROVE  docs' = docs
        BY <1>8, Z3 DEF PerformDelTimeout
    <1>9. ASSUME NEW r \in DOMAIN steps, PerformMiss(r)
          PROVE  docs' = docs
        BY <1>9, Z3 DEF PerformMiss
    <1>10. ASSUME NEW r \in DOMAIN steps, PerformPut(r)
           PROVE  docs' = docs
        BY <1>10, Z3
    <1>11. QED
        <2>1. CASE \E ev \in ExternalEvent : SubmitExternal(ev)
            <3>1. PICK ev \in ExternalEvent : SubmitExternal(ev)
                BY <2>1, Z3
            <3>2. QED
                BY <3>1, <1>1, Z3
        <2>2. CASE \E name \in DOMAIN timeouts : SubmitInternal(name)
            <3>1. PICK name \in DOMAIN timeouts : SubmitInternal(name)
                BY <2>2, Z3
            <3>2. QED
                BY <3>1, <1>2, Z3
        <2>3. CASE \E r \in DOMAIN steps : Process(r)
            <3>1. PICK r \in DOMAIN steps : Process(r)
                BY <2>3, Z3
            <3>2. QED
                BY <3>1, <1>3, Z3
        <2>4. CASE \E r \in DOMAIN steps : Crash(r)
            <3>1. PICK r \in DOMAIN steps : Crash(r)
                BY <2>4, Z3
            <3>2. QED
                BY <3>1, <1>4, Z3
        <2>5. CASE Clock
            BY <2>5, <1>5, Z3
        <2>6. CASE \E r \in DOMAIN steps : Perform(r)
            <3>1. PICK r \in DOMAIN steps : Perform(r)
                BY <2>6, Z3
            <3>2. CASE PerformDone(r)
                BY <3>1, <3>2, <1>6, Z3 DEF Perform
            <3>3. CASE PerformPutTimeout(r)
                BY <3>1, <3>3, <1>7, Z3 DEF Perform
            <3>4. CASE PerformDelTimeout(r)
                BY <3>1, <3>4, <1>8, Z3 DEF Perform
            <3>5. CASE PerformMiss(r)
                BY <3>1, <3>5, <1>9, Z3 DEF Perform
            <3>6. CASE PerformPut(r)
                BY <3>1, <3>6, <1>10, Z3 DEF Perform
            <3>7. QED
                BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, Z3 DEF Perform
        <2>7. QED
            BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, Z3 DEF Next

LEMMA PlaceQuiet ==
    ASSUME Placed, [Next]_vars,
           \A r \in DOMAIN steps : ~PerformPut(r)
    PROVE  Placed'
PROOF
    <1>1. docs' = docs
        <2>1. CASE Next
            BY <2>1, DocStay, Z3
        <2>2. CASE UNCHANGED vars
            BY <2>2, Z3 DEF vars
        <2>3. QED
            BY <2>1, <2>2, Z3
    <1>2. QED
        BY <1>1, PlaceStay, Z3

=============================================================================
