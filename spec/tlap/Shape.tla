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
ASSUME "PromiseSearch" \notin Implemented
ASSUME "TaskSearch" \notin Implemented

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

LEMMA GetOk ==
    ASSUME NEW ev, NEW doc, NEW t, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(HandlePromiseGet(ev, doc, t).doc)
           /\ Home(HandlePromiseGet(ev, doc, t).doc, o)
PROOF
    BY SkipBoth, Isa DEF HandlePromiseGet

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

LEMMA TGetOk ==
    ASSUME NEW ev, NEW doc, NEW t, NEW o,
           DocOk(doc), Home(doc, o)
    PROVE  DocOk(HandleTaskGet(ev, doc, t).doc)
           /\ Home(HandleTaskGet(ev, doc, t).doc, o)
PROOF
    BY SkipBoth, Isa DEF HandleTaskGet

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

=============================================================================
