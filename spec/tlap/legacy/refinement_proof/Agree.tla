------------------------------ MODULE Agree -------------------------------
(* A handler on one document is one result the protocol's handler returns
   for that same map. The sends of a handler are empty: a message is a due
   action. Gets and timeouts are not handlers. *)
EXTENDS Refinement, TLAPS

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

LEMMA ExtCtor ==
    ASSUME NEW S, NEW T, NEW e(_), NEW g(_),
           S = T,
           \A x \in S : e(x) = g(x)
    PROVE  [x \in S |-> e(x)] = [x \in T |-> g(x)]
PROOF
    BY Isa

LEMMA DiffEmpty ==
    ASSUME NEW G
    PROVE  G \ G = {}
PROOF
    BY Z3

LEMMA SameDrop ==
    ASSUME NEW obj
    PROVE  DropListeners(obj) = P!WithoutListeners(obj, obj.promise.listeners)
PROOF
    <1>1. obj.promise.listeners \ obj.promise.listeners = {}
        BY DiffEmpty
    <1>2. QED
        BY <1>1, Zenon DEF DropListeners, P!WithoutListeners

LEMMA SameDropCb ==
    ASSUME NEW obj
    PROVE  DropCallbacks(obj) = P!WithoutCallbacks(obj, obj.promise.callbacks)
PROOF
    <1>1. obj.promise.callbacks \ obj.promise.callbacks = {}
        BY DiffEmpty
    <1>2. QED
        BY <1>1, Zenon DEF DropCallbacks, P!WithoutCallbacks

LEMMA SameWake ==
    ASSUME NEW obj, NEW src, NEW t
    PROVE  Wake(obj, src, t) = P!WakeSuspended(obj, src, t)
PROOF
    BY DEF Wake, P!WakeSuspended, NoTime, P!NoTime

LEMMA SameAdd ==
    ASSUME NEW obj, NEW R
    PROVE  AddResumes(obj, R) = P!UnionResumes(obj, R)
PROOF
    BY DEF AddResumes, P!UnionResumes

LEMMA SameExternal ==
    ASSUME NEW p
    PROVE  IsExternal(p) <=> P!IsExternal(p)
PROOF
    BY DEF IsExternal, P!IsExternal

LEMMA SameNoTime ==
    NoTime = P!NoTime
PROOF
    BY DEF NoTime, P!NoTime

LEMMA SameId ==
    P!Id = Id
PROOF
    BY DEF P!Id, Id

LEMMA SameHorizon ==
    Horizon = P!Horizon
PROOF
    BY DEF Horizon, P!Horizon

LEMMA SameTags ==
    Tags = P!Tags
PROOF
    BY DEF Tags, P!Tags

LEMMA SameSettleState ==
    SettleState = P!SettleState
PROOF
    BY DEF SettleState, P!SettleState

LEMMA SameCreate ==
    CreateReq = P!CreateReq
PROOF
    BY SameId, SameHorizon, SameTags
       DEF CreateReq, P!CreateReq, Id, P!Id, Horizon, P!Horizon, Tags, P!Tags

LEMMA SameSettle ==
    SettleReq = P!SettleReq
PROOF
    BY SameId, SameSettleState
       DEF SettleReq, P!SettleReq, SettleState, P!SettleState, Id, P!Id

LEMMA SettleDoc ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  LET c == HandlePromiseSettle(req, doc, t)
                a == P!HandlePromiseSettle(doc, req, t)
            IN  /\ c.sends = << >>
                /\ IF a = {} THEN c.doc = doc ELSE a = {c.doc}
PROOF
    <1> DEFINE c == HandlePromiseSettle(req, doc, t)
    <1> DEFINE a == P!HandlePromiseSettle(doc, req, t)
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. c = Skip(doc) /\ a = {}
            BY <1>1 DEF c, a, HandlePromiseSettle, P!HandlePromiseSettle
        <2>2. QED
            BY <2>1 DEF Skip
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2>1. old = P!Project(doc[req.id], t)
            BY SameProject DEF old
        <2>2. CASE old.promise.state /= "pending"
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2 DEF c, a, old, HandlePromiseSettle, P!HandlePromiseSettle
            <3>2. QED
                BY <3>1 DEF Skip
        <2>3. CASE old.promise.state = "pending"
            <3>1. a = {c.doc} /\ c.sends = << >>
                BY <1>2, <2>1, <2>3, Isa DEF c, a, old, HandlePromiseSettle,
                       P!HandlePromiseSettle, Write, P!Write,
                       NoTime, P!NoTime, NoTask, P!NoTask
            <3>2. QED
                BY <3>1
        <2>4. QED
            BY <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2

LEMMA CreateDoc ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  LET c == HandlePromiseCreate(req, doc, t)
                a == P!HandlePromiseCreate(doc, req, t)
            IN  /\ c.sends = << >>
                /\ IF a = {} THEN c.doc = doc ELSE a = {c.doc}
PROOF
    <1> DEFINE c == HandlePromiseCreate(req, doc, t)
    <1> DEFINE a == P!HandlePromiseCreate(doc, req, t)
    <1>1. CASE req.id \in DOMAIN doc
        <2>1. c = Skip(doc) /\ a = {}
            BY <1>1 DEF c, a, HandlePromiseCreate, P!HandlePromiseCreate
        <2>2. QED
            BY <2>1 DEF Skip
    <1>2. CASE req.id \notin DOMAIN doc
        <2>1. New(req, t) = P!New(req, t)
            BY SameNew
        <2>2. Write(doc, req.id, New(req, t)) = P!Write(doc, req.id, P!New(req, t))
            BY <2>1, SameWrite
        <2>3. a = {c.doc} /\ c.sends = << >>
            BY <1>2, <2>2 DEF c, a, HandlePromiseCreate, P!HandlePromiseCreate
        <2>4. QED
            BY <2>3
    <1>3. QED
        BY <1>1, <1>2

LEMMA ListenerDoc ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  LET c == HandlePromiseRegisterListener(req, doc, t)
                a == P!HandlePromiseRegisterListener(doc, req, t)
            IN  /\ c.sends = << >>
                /\ IF a = {} THEN c.doc = doc ELSE a = {c.doc}
PROOF
    <1> DEFINE c == HandlePromiseRegisterListener(req, doc, t)
    <1> DEFINE a == P!HandlePromiseRegisterListener(doc, req, t)
    <1>1. CASE req.awaited \notin DOMAIN doc
        <2>1. c = Skip(doc) /\ a = {}
            BY <1>1 DEF c, a, HandlePromiseRegisterListener,
                   P!HandlePromiseRegisterListener
        <2>2. QED
            BY <2>1 DEF Skip
    <1>2. CASE req.awaited \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.awaited], t)
        <2>1. old = P!Project(doc[req.awaited], t)
            BY SameProject DEF old
        <2>1b. IsExternal(old.promise) <=> P!IsExternal(old.promise)
            BY SameExternal
        <2>2. CASE ~IsExternal(old.promise)
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>1b, <2>2 DEF c, a, old,
                       HandlePromiseRegisterListener, P!HandlePromiseRegisterListener
            <3>2. QED
                BY <3>1 DEF Skip
        <2>3. CASE old.promise.state /= "pending"
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>3 DEF c, a, old,
                       HandlePromiseRegisterListener, P!HandlePromiseRegisterListener
            <3>2. QED
                BY <3>1 DEF Skip
        <2>4. CASE IsExternal(old.promise) /\ old.promise.state = "pending"
            <3> DEFINE nw == [old EXCEPT !.promise.listeners = @ \cup {req.address}]
            <3>1. c.doc = Write(doc, req.awaited, nw) /\ c.sends = << >>
                BY <1>2, <2>4 DEF c, old, nw, HandlePromiseRegisterListener
            <3>2. a = {P!Write(doc, req.awaited, nw)}
                BY <1>2, <2>1, <2>1b, <2>4 DEF a, old, nw,
                       P!HandlePromiseRegisterListener
            <3>3. Write(doc, req.awaited, nw) = P!Write(doc, req.awaited, nw)
                BY SameWrite
            <3>4. QED
                BY <3>1, <3>2, <3>3
        <2>5. QED
            BY <2>2, <2>3, <2>4
    <1>3. QED
        BY <1>1, <1>2

LEMMA CallbackDoc ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  LET c == HandlePromiseRegisterCallback(req, doc, t)
                a == P!HandlePromiseRegisterCallback(doc, req, t)
            IN  /\ c.sends = << >>
                /\ IF a = {} THEN c.doc = doc ELSE a = {c.doc}
PROOF
    <1> DEFINE c == HandlePromiseRegisterCallback(req, doc, t)
    <1> DEFINE a == P!HandlePromiseRegisterCallback(doc, req, t)
    <1>1. CASE req.awaited \notin DOMAIN doc \/ req.awaiter \notin DOMAIN doc
        <2>1. c = Skip(doc) /\ a = {}
            BY <1>1 DEF c, a, HandlePromiseRegisterCallback,
                   P!HandlePromiseRegisterCallback
        <2>2. QED
            BY <2>1 DEF Skip
    <1>2. CASE req.awaited \in DOMAIN doc /\ req.awaiter \in DOMAIN doc
        <2> DEFINE awaited == Project(doc[req.awaited], t)
        <2> DEFINE awaiter == Project(doc[req.awaiter], t)
        <2>1. awaited = P!Project(doc[req.awaited], t)
              /\ awaiter = P!Project(doc[req.awaiter], t)
            BY SameProject DEF awaited, awaiter
        <2>1b. IsExternal(awaited.promise) <=> P!IsExternal(awaited.promise)
            BY SameExternal
        <2>2. CASE ~awaiter.promise.tags.targeted
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2 DEF c, a, awaited, awaiter,
                       HandlePromiseRegisterCallback, P!HandlePromiseRegisterCallback
            <3>2. QED
                BY <3>1 DEF Skip
        <2>3. CASE ~IsExternal(awaited.promise)
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>1b, <2>3 DEF c, a, awaited, awaiter,
                       HandlePromiseRegisterCallback, P!HandlePromiseRegisterCallback
            <3>2. QED
                BY <3>1 DEF Skip
        <2>4. CASE awaited.promise.state /= "pending"
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>4 DEF c, a, awaited, awaiter,
                       HandlePromiseRegisterCallback, P!HandlePromiseRegisterCallback
            <3>2. QED
                BY <3>1 DEF Skip
        <2>5. CASE awaiter.promise.state /= "pending"
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>5 DEF c, a, awaited, awaiter,
                       HandlePromiseRegisterCallback, P!HandlePromiseRegisterCallback
            <3>2. QED
                BY <3>1 DEF Skip
        <2>6. CASE awaiter.promise.tags.targeted
                 /\ IsExternal(awaited.promise)
                 /\ awaited.promise.state = "pending"
                 /\ awaiter.promise.state = "pending"
            <3> DEFINE nw == [awaited EXCEPT !.promise.callbacks = @ \cup {req.awaiter}]
            <3>1. c.doc = Write(doc, req.awaited, nw) /\ c.sends = << >>
                BY <1>2, <2>6 DEF c, awaited, awaiter, nw, HandlePromiseRegisterCallback
            <3>2. a = {P!Write(doc, req.awaited, nw)}
                BY <1>2, <2>1, <2>1b, <2>6 DEF a, awaited, awaiter, nw,
                       P!HandlePromiseRegisterCallback
            <3>3. Write(doc, req.awaited, nw) = P!Write(doc, req.awaited, nw)
                BY SameWrite
            <3>4. QED
                BY <3>1, <3>2, <3>3
        <2>7. QED
            BY <2>2, <2>3, <2>4, <2>5, <2>6
    <1>3. QED
        BY <1>1, <1>2

LEMMA AcquireDoc ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  LET c == HandleTaskAcquire(req, doc, t)
                a == P!HandleTaskAcquire(doc, req, t)
            IN  /\ c.sends = << >>
                /\ IF a = {} THEN c.doc = doc ELSE a = {c.doc}
PROOF
    <1> DEFINE c == HandleTaskAcquire(req, doc, t)
    <1> DEFINE a == P!HandleTaskAcquire(doc, req, t)
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. c = Skip(doc) /\ a = {}
            BY <1>1 DEF c, a, HandleTaskAcquire, P!HandleTaskAcquire
        <2>2. QED
            BY <2>1 DEF Skip
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2>1. old = P!Project(doc[req.id], t)
            BY SameProject DEF old
        <2>2. CASE \/ old.task.state /= "pending"
                    \/ old.promise.state /= "pending"
                    \/ old.task.version /= req.version
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2 DEF c, a, old, HandleTaskAcquire, P!HandleTaskAcquire
            <3>2. QED
                BY <3>1 DEF Skip
        <2>3. CASE old.task.state = "pending"
                 /\ old.promise.state = "pending"
                 /\ old.task.version = req.version
            <3> DEFINE nw ==
                    [old EXCEPT !.task.state          = "acquired",
                                !.task.version        = @ + 1,
                                !.task.ttl            = req.ttl,
                                !.task.pid            = req.pid,
                                !.task.leaseTimeoutAt = t + req.ttl,
                                !.task.retryTimeoutAt = NoTime,
                                !.task.resumes        = {}]
            <3>1. c.doc = Write(doc, req.id, nw) /\ c.sends = << >>
                BY <1>2, <2>3 DEF c, old, nw, HandleTaskAcquire
            <3>2. nw = [old EXCEPT !.task.state          = "acquired",
                                   !.task.version        = @ + 1,
                                   !.task.ttl            = req.ttl,
                                   !.task.pid            = req.pid,
                                   !.task.leaseTimeoutAt = t + req.ttl,
                                   !.task.retryTimeoutAt = P!NoTime,
                                   !.task.resumes        = {}]
                BY SameNoTime DEF nw
            <3>3. a = {P!Write(doc, req.id, nw)}
                BY <1>2, <2>1, <2>3, <3>2 DEF a, old, nw, P!HandleTaskAcquire
            <3>4. Write(doc, req.id, nw) = P!Write(doc, req.id, nw)
                BY SameWrite
            <3>5. QED
                BY <3>1, <3>3, <3>4
        <2>4. QED
            BY <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2

LEMMA ReleaseDoc ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  LET c == HandleTaskRelease(req, doc, t)
                a == P!HandleTaskRelease(doc, req, t)
            IN  /\ c.sends = << >>
                /\ IF a = {} THEN c.doc = doc ELSE a = {c.doc}
PROOF
    <1> DEFINE c == HandleTaskRelease(req, doc, t)
    <1> DEFINE a == P!HandleTaskRelease(doc, req, t)
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. c = Skip(doc) /\ a = {}
            BY <1>1 DEF c, a, HandleTaskRelease, P!HandleTaskRelease
        <2>2. QED
            BY <2>1 DEF Skip
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2>1. old = P!Project(doc[req.id], t)
            BY SameProject DEF old
        <2>2. CASE \/ old.task.state /= "acquired"
                    \/ old.promise.state /= "pending"
                    \/ old.task.version /= req.version
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2 DEF c, a, old, HandleTaskRelease, P!HandleTaskRelease
            <3>2. QED
                BY <3>1 DEF Skip
        <2>3. CASE old.task.state = "acquired"
                 /\ old.promise.state = "pending"
                 /\ old.task.version = req.version
            <3>1. a = {c.doc} /\ c.sends = << >>
                BY <1>2, <2>1, <2>3, Isa DEF c, a, old, HandleTaskRelease,
                       P!HandleTaskRelease, Write, P!Write, NoTime, P!NoTime
            <3>2. QED
                BY <3>1
        <2>4. QED
            BY <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2

LEMMA HaltDoc ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  LET c == HandleTaskHalt(req, doc, t)
                a == P!HandleTaskHalt(doc, req, t)
            IN  /\ c.sends = << >>
                /\ IF a = {} THEN c.doc = doc ELSE a = {c.doc}
PROOF
    <1> DEFINE c == HandleTaskHalt(req, doc, t)
    <1> DEFINE a == P!HandleTaskHalt(doc, req, t)
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. c = Skip(doc) /\ a = {}
            BY <1>1 DEF c, a, HandleTaskHalt, P!HandleTaskHalt
        <2>2. QED
            BY <2>1 DEF Skip
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2>1. old = P!Project(doc[req.id], t)
            BY SameProject DEF old
        <2>2. CASE old.task.state \in {"none", "fulfilled", "halted"}
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2 DEF c, a, old, HandleTaskHalt, P!HandleTaskHalt
            <3>2. QED
                BY <3>1 DEF Skip
        <2>3. CASE old.task.state \notin {"none", "fulfilled", "halted"}
            <3>1. a = {c.doc} /\ c.sends = << >>
                BY <1>2, <2>1, <2>3, Isa DEF c, a, old, HandleTaskHalt,
                       P!HandleTaskHalt, Write, P!Write, NoTime, P!NoTime
            <3>2. QED
                BY <3>1
        <2>4. QED
            BY <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2

LEMMA ContinueDoc ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  LET c == HandleTaskContinue(req, doc, t)
                a == P!HandleTaskContinue(doc, req, t)
            IN  /\ c.sends = << >>
                /\ IF a = {} THEN c.doc = doc ELSE a = {c.doc}
PROOF
    <1> DEFINE c == HandleTaskContinue(req, doc, t)
    <1> DEFINE a == P!HandleTaskContinue(doc, req, t)
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. c = Skip(doc) /\ a = {}
            BY <1>1 DEF c, a, HandleTaskContinue, P!HandleTaskContinue
        <2>2. QED
            BY <2>1 DEF Skip
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2>1. old = P!Project(doc[req.id], t)
            BY SameProject DEF old
        <2>2. CASE old.task.state /= "halted" \/ old.promise.state /= "pending"
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2 DEF c, a, old, HandleTaskContinue, P!HandleTaskContinue
            <3>2. QED
                BY <3>1 DEF Skip
        <2>3. CASE old.task.state = "halted" /\ old.promise.state = "pending"
            <3>1. a = {c.doc} /\ c.sends = << >>
                BY <1>2, <2>1, <2>3, Isa DEF c, a, old, HandleTaskContinue,
                       P!HandleTaskContinue, Write, P!Write, NoTime, P!NoTime
            <3>2. QED
                BY <3>1
        <2>4. QED
            BY <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2

LEMMA FulfillDoc ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  LET c == HandleTaskFulfill(req, doc, t)
                a == P!HandleTaskFulfill(doc, req, t)
            IN  /\ c.sends = << >>
                /\ IF a = {} THEN c.doc = doc ELSE a = {c.doc}
PROOF
    <1> DEFINE c == HandleTaskFulfill(req, doc, t)
    <1> DEFINE a == P!HandleTaskFulfill(doc, req, t)
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. c = Skip(doc) /\ a = {}
            BY <1>1 DEF c, a, HandleTaskFulfill, P!HandleTaskFulfill
        <2>2. QED
            BY <2>1 DEF Skip
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2>1. old = P!Project(doc[req.id], t)
            BY SameProject DEF old
        <2>2. CASE \/ old.task.state /= "acquired"
                    \/ old.promise.state /= "pending"
                    \/ old.task.version /= req.version
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2 DEF c, a, old, HandleTaskFulfill, P!HandleTaskFulfill
            <3>2. QED
                BY <3>1 DEF Skip
        <2>3. CASE old.task.state = "acquired"
                 /\ old.promise.state = "pending"
                 /\ old.task.version = req.version
            <3>1. a = {c.doc} /\ c.sends = << >>
                BY <1>2, <2>1, <2>3, Isa DEF c, a, old, HandleTaskFulfill,
                       P!HandleTaskFulfill, Write, P!Write,
                       NoTime, P!NoTime, NoTask, P!NoTask
            <3>2. QED
                BY <3>1
        <2>4. QED
            BY <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2

LEMMA HeldSame ==
    ASSUME NEW obj, NEW ttl, NEW pid, NEW t
    PROVE  [obj EXCEPT !.task.state          = "acquired",
                       !.task.version        = @ + 1,
                       !.task.ttl            = ttl,
                       !.task.pid            = pid,
                       !.task.leaseTimeoutAt = t + ttl,
                       !.task.retryTimeoutAt = NoTime,
                       !.task.resumes        = {}]
              = [obj EXCEPT !.task.state          = "acquired",
                            !.task.version        = @ + 1,
                            !.task.ttl            = ttl,
                            !.task.pid            = pid,
                            !.task.leaseTimeoutAt = t + ttl,
                            !.task.retryTimeoutAt = P!NoTime,
                            !.task.resumes        = {}]
PROOF
    BY SameNoTime

LEMMA TaskMake ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  LET c == HandleTaskCreate(req, doc, t)
                a == P!HandleTaskCreate(doc, req, t)
            IN  /\ c.sends = << >>
                /\ IF a = {} THEN c.doc = doc ELSE a = {c.doc}
PROOF
    <1> DEFINE c == HandleTaskCreate(req, doc, t)
    <1> DEFINE a == P!HandleTaskCreate(doc, req, t)
    <1> DEFINE id == req.action.id
    <1>1. CASE ~req.action.tags.targeted
        <2>1. c = Skip(doc) /\ a = {}
            BY <1>1 DEF c, a, id, HandleTaskCreate, P!HandleTaskCreate
        <2>2. QED
            BY <2>1 DEF Skip
    <1>2. CASE req.action.tags.targeted /\ id \notin DOMAIN doc
        <2> DEFINE born == New(req.action, t)
        <2> DEFINE held ==
                [born EXCEPT !.task.state          = "acquired",
                             !.task.version        = @ + 1,
                             !.task.ttl            = req.ttl,
                             !.task.pid            = req.pid,
                             !.task.leaseTimeoutAt = t + req.ttl,
                             !.task.retryTimeoutAt = NoTime,
                             !.task.resumes        = {}]
        <2>1. born = P!New(req.action, t)
            BY SameNew DEF born
        <2>2. held = [born EXCEPT !.task.state          = "acquired",
                                   !.task.version        = @ + 1,
                                   !.task.ttl            = req.ttl,
                                   !.task.pid            = req.pid,
                                   !.task.leaseTimeoutAt = t + req.ttl,
                                   !.task.retryTimeoutAt = P!NoTime,
                                   !.task.resumes        = {}]
            BY SameNoTime DEF held
        <2> DEFINE body == IF born.promise.state = "pending" THEN held ELSE born
        <2>3. c.doc = Write(doc, id, body) /\ c.sends = << >>
            BY <1>2 DEF c, id, born, held, body, HandleTaskCreate
        <2>4. a = {P!Write(doc, id, body)}
            BY <1>2, <2>1, <2>2 DEF a, id, born, held, body, P!HandleTaskCreate
        <2>5. Write(doc, id, body) = P!Write(doc, id, body)
            BY SameWrite
        <2>6. QED
            BY <2>3, <2>4, <2>5 DEF body
    <1>3. CASE req.action.tags.targeted /\ id \in DOMAIN doc
        <2> DEFINE old == Project(doc[id], t)
        <2>1. old = P!Project(doc[id], t)
            BY SameProject DEF old
        <2>2. CASE ~old.promise.tags.targeted \/ old.task.state /= "pending"
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>3, <2>1, <2>2 DEF c, a, id, old, HandleTaskCreate, P!HandleTaskCreate
            <3>2. QED
                BY <3>1 DEF Skip
        <2>3. CASE old.promise.tags.targeted /\ old.task.state = "pending"
            <3> DEFINE nw ==
                    [old EXCEPT !.task.state          = "acquired",
                                !.task.version        = @ + 1,
                                !.task.ttl            = req.ttl,
                                !.task.pid            = req.pid,
                                !.task.leaseTimeoutAt = t + req.ttl,
                                !.task.retryTimeoutAt = NoTime,
                                !.task.resumes        = {}]
            <3>1. c.doc = Write(doc, id, nw) /\ c.sends = << >>
                BY <1>3, <2>3 DEF c, id, old, nw, HandleTaskCreate
            <3>2. nw = [old EXCEPT !.task.state          = "acquired",
                                   !.task.version        = @ + 1,
                                   !.task.ttl            = req.ttl,
                                   !.task.pid            = req.pid,
                                   !.task.leaseTimeoutAt = t + req.ttl,
                                   !.task.retryTimeoutAt = P!NoTime,
                                   !.task.resumes        = {}]
                BY SameNoTime DEF nw
            <3>3. a = {P!Write(doc, id, nw)}
                BY <1>3, <2>1, <2>3, <3>2 DEF a, id, old, nw, P!HandleTaskCreate
            <3>4. Write(doc, id, nw) = P!Write(doc, id, nw)
                BY SameWrite
            <3>5. QED
                BY <3>1, <3>3, <3>4
        <2>4. QED
            BY <2>2, <2>3
    <1>4. QED
        BY <1>1, <1>2, <1>3 DEF id

LEMMA SameBeat ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  { i \in DOMAIN doc :
               LET old == Project(doc[i], t)
               IN  /\ \E rf \in req.tasks :
                         rf.id = i /\ rf.version = old.task.version
                   /\ old.task.state = "acquired"
                   /\ old.task.pid = req.pid
                   /\ old.promise.state = "pending" }
              = { i \in DOMAIN doc :
                    LET old == P!Project(doc[i], t)
                    IN  /\ \E rf \in req.tasks :
                              rf.id = i /\ rf.version = old.task.version
                        /\ old.task.state = "acquired"
                        /\ old.task.pid = req.pid
                        /\ old.promise.state = "pending" }
PROOF
    <1> DEFINE beatc ==
            { i \in DOMAIN doc :
                LET old == Project(doc[i], t)
                IN  /\ \E rf \in req.tasks :
                          rf.id = i /\ rf.version = old.task.version
                    /\ old.task.state = "acquired"
                    /\ old.task.pid = req.pid
                    /\ old.promise.state = "pending" }
    <1> DEFINE beata ==
            { i \in DOMAIN doc :
                LET old == P!Project(doc[i], t)
                IN  /\ \E rf \in req.tasks :
                          rf.id = i /\ rf.version = old.task.version
                    /\ old.task.state = "acquired"
                    /\ old.task.pid = req.pid
                    /\ old.promise.state = "pending" }
    <1>1. \A i : i \in beatc <=> i \in beata
        <2> SUFFICES ASSUME NEW i
                     PROVE  i \in beatc <=> i \in beata
            OBVIOUS
        <2>1. CASE i \notin DOMAIN doc
            BY <2>1 DEF beatc, beata
        <2>2. CASE i \in DOMAIN doc
            <3>1. Project(doc[i], t) = P!Project(doc[i], t)
                BY SameProject
            <3>2. QED
                BY <2>2, <3>1, Zenon DEF beatc, beata
        <2>3. QED
            BY <2>1, <2>2
    <1>2. QED
        BY <1>1, SetExtensionality DEF beatc, beata

LEMMA HeartbeatDoc ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  LET c == HandleTaskHeartbeat(req, doc, t)
                a == P!HandleTaskHeartbeat(doc, req, t)
            IN  /\ c.sends = << >>
                /\ IF a = {} THEN c.doc = doc ELSE c.doc \in a
PROOF
    <1> DEFINE c == HandleTaskHeartbeat(req, doc, t)
    <1> DEFINE a == P!HandleTaskHeartbeat(doc, req, t)
    <1> DEFINE beat ==
            { i \in DOMAIN doc :
                LET old == Project(doc[i], t)
                IN  /\ \E rf \in req.tasks :
                          rf.id = i /\ rf.version = old.task.version
                    /\ old.task.state = "acquired"
                    /\ old.task.pid = req.pid
                    /\ old.promise.state = "pending" }
    <1> DEFINE upd(i) ==
            LET old == Project(doc[i], t)
            IN  [old EXCEPT !.task.leaseTimeoutAt = t + old.task.ttl]
    <1> DEFINE upda(i) ==
            LET old == P!Project(doc[i], t)
            IN  [old EXCEPT !.task.leaseTimeoutAt = t + old.task.ttl]
    <1> DEFINE at(keep) ==
            [ i \in DOMAIN doc |-> IF i \in keep THEN upd(i) ELSE doc[i] ]
    <1> DEFINE ata(keep) ==
            [ i \in DOMAIN doc |-> IF i \in keep THEN upda(i) ELSE doc[i] ]
    <1>1. beat
            = { i \in DOMAIN doc :
                  LET old == P!Project(doc[i], t)
                  IN  /\ \E rf \in req.tasks :
                            rf.id = i /\ rf.version = old.task.version
                      /\ old.task.state = "acquired"
                      /\ old.task.pid = req.pid
                      /\ old.promise.state = "pending" }
        BY SameBeat DEF beat
    <1>2. \A i \in DOMAIN doc : upd(i) = upda(i)
        <2> SUFFICES ASSUME NEW i \in DOMAIN doc
                     PROVE  upd(i) = upda(i)
            OBVIOUS
        <2>1. Project(doc[i], t) = P!Project(doc[i], t)
            BY SameProject
        <2>2. QED
            BY <2>1 DEF upd, upda
    <1>3. \A keep : at(keep) = ata(keep)
        <2> SUFFICES ASSUME NEW keep
                     PROVE  at(keep) = ata(keep)
            OBVIOUS
        <2>0. DOMAIN doc = DOMAIN doc
            OBVIOUS
        <2>1. \A i \in DOMAIN doc :
                (IF i \in keep THEN upd(i) ELSE doc[i])
                  = (IF i \in keep THEN upda(i) ELSE doc[i])
            BY <1>2
        <2>2. QED
            BY <2>0, <2>1, ExtCtor DEF at, ata
    <1>4. CASE beat = {}
        <2>1. c = Skip(doc)
            BY <1>4 DEF c, beat, HandleTaskHeartbeat
        <2>2. a = {}
            BY <1>1, <1>4 DEF a, P!HandleTaskHeartbeat
        <2>3. QED
            BY <2>1, <2>2 DEF Skip
    <1>5. CASE beat # {}
        <2>1. c.doc = at(beat) /\ c.sends = << >>
            BY <1>5 DEF c, beat, upd, at, HandleTaskHeartbeat
        <2>2. a = {ata(beat)}
                  \cup { ata({ j \in beat : j.origin = p }) : p \in Origin }
            BY <1>1, <1>5 DEF a, upda, ata, P!HandleTaskHeartbeat
        <2>3. at(beat) = ata(beat)
            BY <1>3
        <2>4. at(beat) \in a
            BY <2>2, <2>3
        <2>5. QED
            BY <2>1, <2>4
    <1>6. QED
        BY <1>4, <1>5

LEMMA ExtSame ==
    ASSUME NEW doc, NEW t, NEW aw
    PROVE  (\E a \in aw : ~IsExternal(Project(doc[a], t).promise))
              <=> (\E a \in aw : ~P!IsExternal(P!Project(doc[a], t).promise))
PROOF
    <1>1. \A a \in aw :
            IsExternal(Project(doc[a], t).promise)
              <=> P!IsExternal(P!Project(doc[a], t).promise)
        <2> SUFFICES ASSUME NEW a \in aw
                     PROVE  IsExternal(Project(doc[a], t).promise)
                               <=> P!IsExternal(P!Project(doc[a], t).promise)
            OBVIOUS
        <2>1. Project(doc[a], t) = P!Project(doc[a], t)
            BY SameProject
        <2>2. Project(doc[a], t).promise = P!Project(doc[a], t).promise
            BY <2>1
        <2>3. QED
            BY <2>2, SameExternal
    <1>2. QED
        BY <1>1

LEMMA StateSame ==
    ASSUME NEW doc, NEW t, NEW aw
    PROVE  (\E a \in aw : Project(doc[a], t).promise.state /= "pending")
              <=> (\E a \in aw : P!Project(doc[a], t).promise.state /= "pending")
PROOF
    <1>1. \A a \in aw :
            Project(doc[a], t).promise.state = P!Project(doc[a], t).promise.state
        <2> SUFFICES ASSUME NEW a \in aw
                     PROVE  Project(doc[a], t).promise.state
                               = P!Project(doc[a], t).promise.state
            OBVIOUS
        <2>1. Project(doc[a], t) = P!Project(doc[a], t)
            BY SameProject
        <2>2. QED
            BY <2>1
    <1>2. QED
        BY <1>1

LEMMA MissSome ==
    ASSUME NEW aw, NEW dom
    PROVE  { a \in aw : a \in dom } /= aw <=> \E a \in aw : a \notin dom
PROOF
    BY Z3

LEMMA TakeElse ==
    ASSUME NEW cond, NEW yes, NEW no, ~cond
    PROVE  (IF cond THEN yes ELSE no) = no
PROOF
    BY Zenon

LEMMA SuspendOpen ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  P!HandleTaskSuspend(doc, req, t)
              = LET aw == {a.awaited : a \in req.actions}
                IN  IF \/ req.actions = {}
                       \/ req.id \in aw
                       \/ \E a \in aw : a.origin /= req.id.origin
                       \/ req.id \notin DOMAIN doc
                       \/ \E a \in aw : a \notin DOMAIN doc
                    THEN {}
                    ELSE LET old == P!Project(doc[req.id], t)
                         IN  IF \/ old.task.state /= "acquired"
                                \/ old.promise.state /= "pending"
                                \/ old.task.version /= req.version
                                \/ \E a \in aw : ~P!IsExternal(P!Project(doc[a], t).promise)
                             THEN {}
                             ELSE IF \E a \in aw : P!Project(doc[a], t).promise.state /= "pending"
                                  THEN {P!Write(doc, req.id, [old EXCEPT !.task.resumes = {}])}
                                  ELSE {[ i \in DOMAIN doc |->
                                            IF i = req.id THEN
                                                [old EXCEPT !.task.state          = "suspended",
                                                            !.task.pid            = NoPid,
                                                            !.task.ttl            = P!NoTime,
                                                            !.task.leaseTimeoutAt = P!NoTime,
                                                            !.task.retryTimeoutAt = P!NoTime,
                                                            !.task.resumes        = {}]
                                            ELSE IF i \in aw THEN
                                                [P!Project(doc[i], t) EXCEPT
                                                     !.promise.callbacks = @ \cup {req.id}]
                                            ELSE doc[i] ]}
PROOF
    BY ONLY DEF P!HandleTaskSuspend

LEMMA SuspendAt ==
    ASSUME NEW req, NEW doc, NEW t, NEW aw0, NEW old0,
           aw0 = {x.awaited : x \in req.actions},
           old0 = P!Project(doc[req.id], t),
           ~ (\/ req.actions = {}
              \/ req.id \in aw0
              \/ \E x \in aw0 : x.origin /= req.id.origin
              \/ req.id \notin DOMAIN doc
              \/ \E x \in aw0 : x \notin DOMAIN doc),
           ~ (\/ old0.task.state /= "acquired"
              \/ old0.promise.state /= "pending"
              \/ old0.task.version /= req.version
              \/ \E x \in aw0 : ~P!IsExternal(P!Project(doc[x], t).promise)),
           ~ (\E x \in aw0 : P!Project(doc[x], t).promise.state /= "pending")
    PROVE  P!HandleTaskSuspend(doc, req, t)
              = {[ i \in DOMAIN doc |->
                    IF i = req.id THEN
                        [old0 EXCEPT !.task.state          = "suspended",
                                     !.task.pid            = NoPid,
                                     !.task.ttl            = P!NoTime,
                                     !.task.leaseTimeoutAt = P!NoTime,
                                     !.task.retryTimeoutAt = P!NoTime,
                                     !.task.resumes        = {}]
                    ELSE IF i \in aw0 THEN
                        [P!Project(doc[i], t) EXCEPT
                             !.promise.callbacks = @ \cup {req.id}]
                    ELSE doc[i] ]}
PROOF
    BY SuspendOpen, Zenon DEF SuspendOpen

LEMMA SuspendDoc ==
    ASSUME NEW req, NEW doc, NEW t
    PROVE  LET c == HandleTaskSuspend(req, doc, t)
                abs == P!HandleTaskSuspend(doc, req, t)
            IN  /\ c.sends = << >>
                /\ IF abs = {} THEN c.doc = doc ELSE abs = {c.doc}
PROOF
    <1> DEFINE c == HandleTaskSuspend(req, doc, t)
    <1> DEFINE abs == P!HandleTaskSuspend(doc, req, t)
    <1> DEFINE aw == { x.awaited : x \in req.actions }
    <1> DEFINE seen == { x \in aw : x \in DOMAIN doc }
    <1>1. CASE \/ req.actions = {}
                \/ req.id \in aw
                \/ \E x \in aw : x.origin /= req.id.origin
                \/ req.id \notin DOMAIN doc
                \/ seen /= aw
        <2>1. seen /= aw <=> \E x \in aw : x \notin DOMAIN doc
            BY MissSome DEF seen
        <2>2. c = Skip(doc) /\ abs = {}
            BY <1>1, <2>1 DEF c, abs, aw, seen, HandleTaskSuspend, P!HandleTaskSuspend
        <2>3. QED
            BY <2>2 DEF Skip
    <1>2. CASE req.actions /= {}
             /\ req.id \notin aw
             /\ \A x \in aw : x.origin = req.id.origin
             /\ req.id \in DOMAIN doc
             /\ seen = aw
        <2> DEFINE old == Project(doc[req.id], t)
        <2>1. old = P!Project(doc[req.id], t)
            BY SameProject DEF old
        <2>1b. (\E x \in aw : ~IsExternal(Project(doc[x], t).promise))
                 <=> (\E x \in aw : ~P!IsExternal(P!Project(doc[x], t).promise))
            BY ExtSame DEF aw
        <2>1c. (\E x \in aw : Project(doc[x], t).promise.state /= "pending")
                 <=> (\E x \in aw : P!Project(doc[x], t).promise.state /= "pending")
            BY StateSame DEF aw
        <2>1d. \A x \in aw : x \in DOMAIN doc
            BY <1>2, MissSome DEF seen
        <2>2. CASE \/ old.task.state /= "acquired"
                    \/ old.promise.state /= "pending"
                    \/ old.task.version /= req.version
                    \/ \E x \in aw : ~IsExternal(Project(doc[x], t).promise)
            <3>1. c = Skip(doc) /\ abs = {}
                BY <1>2, <2>1, <2>1b, <2>2 DEF c, abs, aw, old, seen,
                       HandleTaskSuspend, P!HandleTaskSuspend
            <3>2. QED
                BY <3>1 DEF Skip
        <2>3. CASE old.task.state = "acquired"
                 /\ old.promise.state = "pending"
                 /\ old.task.version = req.version
                 /\ \A x \in aw : IsExternal(Project(doc[x], t).promise)
                 /\ \E x \in aw : Project(doc[x], t).promise.state /= "pending"
            <3> DEFINE nw == [old EXCEPT !.task.resumes = {}]
            <3>1. c.doc = Write(doc, req.id, nw) /\ c.sends = << >>
                BY <1>2, <2>1b, <2>1c, <2>3 DEF c, aw, old, seen, nw, HandleTaskSuspend
            <3>2. abs = {P!Write(doc, req.id, nw)}
                BY <1>2, <2>1, <2>1b, <2>1c, <2>1d, <2>3
                   DEF abs, aw, old, nw, P!HandleTaskSuspend
            <3>3. Write(doc, req.id, nw) = P!Write(doc, req.id, nw)
                BY SameWrite
            <3>4. QED
                BY <3>1, <3>2, <3>3
        <2>4. CASE old.task.state = "acquired"
                 /\ old.promise.state = "pending"
                 /\ old.task.version = req.version
                 /\ \A x \in aw : IsExternal(Project(doc[x], t).promise)
                 /\ \A x \in aw : Project(doc[x], t).promise.state = "pending"
            <3> DEFINE nw ==
                    [old EXCEPT !.task.state          = "suspended",
                                !.task.pid            = NoPid,
                                !.task.ttl            = NoTime,
                                !.task.leaseTimeoutAt = NoTime,
                                !.task.retryTimeoutAt = NoTime,
                                !.task.resumes        = {}]
            <3>1. nw = [old EXCEPT !.task.state          = "suspended",
                                   !.task.pid            = NoPid,
                                   !.task.ttl            = P!NoTime,
                                   !.task.leaseTimeoutAt = P!NoTime,
                                   !.task.retryTimeoutAt = P!NoTime,
                                   !.task.resumes        = {}]
                BY SameNoTime DEF nw
            <3> DEFINE fn ==
                    [ i \in DOMAIN doc |->
                        IF i = req.id THEN nw
                        ELSE IF i \in aw THEN
                            [Project(doc[i], t) EXCEPT !.promise.callbacks = @ \cup {req.id}]
                        ELSE doc[i] ]
            <3>2. c.doc = fn /\ c.sends = << >>
                BY <1>2, <2>1b, <2>1c, <2>4 DEF c, aw, old, seen, nw, fn, HandleTaskSuspend
            <3>2b. /\ P!Project(doc[req.id], t).task.state = "acquired"
                   /\ P!Project(doc[req.id], t).promise.state = "pending"
                   /\ P!Project(doc[req.id], t).task.version = req.version
                BY <2>1, <2>4 DEF old
            <3>3a. ~ \E x \in aw : ~P!IsExternal(P!Project(doc[x], t).promise)
                BY <2>1b, <2>4
            <3>3b. ~ \E x \in aw : P!Project(doc[x], t).promise.state /= "pending"
                BY <2>1c, <2>4
            <3>3c. ~ (\/ req.actions = {}
                      \/ req.id \in aw
                      \/ \E x \in aw : x.origin /= req.id.origin
                      \/ req.id \notin DOMAIN doc
                      \/ \E x \in aw : x \notin DOMAIN doc)
                BY <1>2, <2>1d
            <3>3d. ~ (\/ P!Project(doc[req.id], t).task.state /= "acquired"
                      \/ P!Project(doc[req.id], t).promise.state /= "pending"
                      \/ P!Project(doc[req.id], t).task.version /= req.version
                      \/ \E x \in aw : ~P!IsExternal(P!Project(doc[x], t).promise))
                BY <3>2b, <3>3a
            <3>3. abs = { [ i \in DOMAIN doc |->
                           IF i = req.id THEN
                               [P!Project(doc[req.id], t) EXCEPT
                                    !.task.state          = "suspended",
                                    !.task.pid            = NoPid,
                                    !.task.ttl            = P!NoTime,
                                    !.task.leaseTimeoutAt = P!NoTime,
                                    !.task.retryTimeoutAt = P!NoTime,
                                    !.task.resumes        = {}]
                           ELSE IF i \in aw THEN
                               [P!Project(doc[i], t) EXCEPT
                                    !.promise.callbacks = @ \cup {req.id}]
                           ELSE doc[i] ] }
                BY <2>1, <3>2b, <3>3b, <3>3c, <3>3d, SuspendAt DEF abs, aw, old
            <3>4. \A i \in DOMAIN doc : Project(doc[i], t) = P!Project(doc[i], t)
                <4> SUFFICES ASSUME NEW i \in DOMAIN doc
                             PROVE  Project(doc[i], t) = P!Project(doc[i], t)
                    OBVIOUS
                <4>1. QED
                    BY SameProject
            <3>5. fn = [ i \in DOMAIN doc |->
                          IF i = req.id THEN
                              [old EXCEPT !.task.state          = "suspended",
                                          !.task.pid            = NoPid,
                                          !.task.ttl            = P!NoTime,
                                          !.task.leaseTimeoutAt = P!NoTime,
                                          !.task.retryTimeoutAt = P!NoTime,
                                          !.task.resumes        = {}]
                          ELSE IF i \in aw THEN
                              [P!Project(doc[i], t) EXCEPT
                                   !.promise.callbacks = @ \cup {req.id}]
                          ELSE doc[i] ]
                BY <3>1, <3>4, Zenon DEF fn
            <3>6. abs = {fn}
                BY <2>1, <3>3, <3>5 DEF old
            <3>7. QED
                BY <3>2, <3>6
        <2>5. QED
            BY <2>2, <2>3, <2>4
    <1>3. QED
        BY <1>1, <1>2

LEMMA FenceKind ==
    ASSUME NEW act, act \in FenceAction
    PROVE  \/ /\ act.tag = "Create"
              /\ act.req \in CreateReq
           \/ /\ act.tag = "Settle"
              /\ act.req \in SettleReq
PROOF
    <1>1. CASE act \in { [tag |-> "Create", req |-> r] : r \in CreateReq }
        <2>1. PICK r \in CreateReq : act = [tag |-> "Create", req |-> r]
            BY <1>1
        <2>2. QED
            BY <2>1
    <1>2. CASE act \in { [tag |-> "Settle", req |-> r] : r \in SettleReq }
        <2>1. PICK r \in SettleReq : act = [tag |-> "Settle", req |-> r]
            BY <1>2
        <2>2. QED
            BY <2>1
    <1>3. QED
        BY <1>1, <1>2 DEF FenceAction

LEMMA CreateIn ==
    ASSUME NEW doc, NEW t, NEW Rs, NEW r, NEW y,
           Rs # {},
           r \in Rs,
           y \in P!HandlePromiseCreate(doc, r, t)
    PROVE  y \in P!Flat({ P!HandlePromiseCreate(doc, q, t) : q \in Rs })
PROOF
    <1>1. y \in UNION { P!HandlePromiseCreate(doc, q, t) : q \in Rs }
        BY Zenon
    <1>2. { P!HandlePromiseCreate(doc, q, t) : q \in Rs } # {}
        BY Z3
    <1>3. QED
        BY <1>1, <1>2 DEF P!Flat

LEMMA SettleIn ==
    ASSUME NEW doc, NEW t, NEW Rs, NEW r, NEW y,
           Rs # {},
           r \in Rs,
           y \in P!HandlePromiseSettle(doc, r, t)
    PROVE  y \in P!Flat({ P!HandlePromiseSettle(doc, q, t) : q \in Rs })
PROOF
    <1>1. y \in UNION { P!HandlePromiseSettle(doc, q, t) : q \in Rs }
        BY Zenon
    <1>2. { P!HandlePromiseSettle(doc, q, t) : q \in Rs } # {}
        BY Z3
    <1>3. QED
        BY <1>1, <1>2 DEF P!Flat

LEMMA FenceDoc ==
    ASSUME NEW req, NEW doc, NEW t,
           req.action \in FenceAction
    PROVE  LET c == HandleTaskFence(req, doc, t)
                a == P!HandleTaskFence(doc, req.id, req.version, t)
            IN  /\ c.sends = << >>
                /\ c.doc = doc \/ c.doc \in a
PROOF
    <1> DEFINE c == HandleTaskFence(req, doc, t)
    <1> DEFINE a == P!HandleTaskFence(doc, req.id, req.version, t)
    <1> DEFINE nested == req.action.req
    <1>1. CASE req.id \notin DOMAIN doc
        <2>1. c = Skip(doc)
            BY <1>1 DEF c, HandleTaskFence
        <2>2. QED
            BY <2>1 DEF Skip
    <1>2. CASE req.id \in DOMAIN doc
        <2> DEFINE old == Project(doc[req.id], t)
        <2>1. old = P!Project(doc[req.id], t)
            BY SameProject DEF old
        <2>2. CASE \/ nested.id = req.id
                    \/ nested.id.origin /= req.id.origin
                    \/ old.task.state /= "acquired"
                    \/ old.promise.state /= "pending"
                    \/ old.task.version /= req.version
            <3>1. c = Skip(doc)
                BY <1>2, <2>2 DEF c, old, nested, HandleTaskFence
            <3>2. QED
                BY <3>1 DEF Skip
        <2>3. CASE nested.id /= req.id
                 /\ nested.id.origin = req.id.origin
                 /\ old.task.state = "acquired"
                 /\ old.promise.state = "pending"
                 /\ old.task.version = req.version
                 /\ req.action.tag = "Create"
            <3> DEFINE cc == HandlePromiseCreate(nested, doc, t)
            <3> DEFINE aa == P!HandlePromiseCreate(doc, nested, t)
            <3> DEFINE Rs == { r \in CreateReq : r.id /= req.id }
            <3>1. cc.sends = << >>
                    /\ IF aa = {} THEN cc.doc = doc ELSE aa = {cc.doc}
                <4>1. LET u == HandlePromiseCreate(nested, doc, t)
                          v == P!HandlePromiseCreate(doc, nested, t)
                      IN  u.sends = << >>
                          /\ IF v = {} THEN u.doc = doc ELSE v = {u.doc}
                    BY CreateDoc
                <4>2. QED
                    BY <4>1 DEF cc, aa
            <3>2. c = cc
                BY <1>2, <2>3 DEF c, cc, old, nested, HandleTaskFence
            <3>3. \/ /\ req.action.tag = "Create"
                     /\ req.action.req \in CreateReq
                  \/ /\ req.action.tag = "Settle"
                     /\ req.action.req \in SettleReq
                BY FenceKind
            <3>3b. nested \in CreateReq
                BY <2>3, <3>3 DEF nested
            <3>4. nested \in Rs
                BY <2>3, <3>3b DEF nested, Rs
            <3>5. CASE aa = {}
                BY <3>1, <3>2, <3>5 DEF cc
            <3>6. CASE aa # {}
                <4>1. aa = {cc.doc}
                    BY <3>1, <3>6
                <4>2. cc.doc \in aa
                    BY <4>1
                <4>3. cc.doc \in P!Flat({ P!HandlePromiseCreate(doc, q, t) : q \in Rs })
                    BY <3>4, <4>2, CreateIn DEF aa
                <4>4. a = P!Flat({ P!HandlePromiseCreate(doc, q, t) : q \in Rs })
                        \cup P!Flat({ P!HandlePromiseSettle(doc, q, t) :
                                       q \in { r \in SettleReq : r.id /= req.id } })
                    BY <1>2, <2>1, <2>3, SameCreate, SameSettle
                       DEF a, old, Rs, SameCreate, SameSettle, P!HandleTaskFence
                <4>5. cc.doc \in a
                    BY <4>3, <4>4
                <4>6. QED
                    BY <3>1, <3>2, <4>5 DEF cc
            <3>7. QED
                BY <3>5, <3>6
        <2>4. CASE nested.id /= req.id
                 /\ nested.id.origin = req.id.origin
                 /\ old.task.state = "acquired"
                 /\ old.promise.state = "pending"
                 /\ old.task.version = req.version
                 /\ req.action.tag = "Settle"
            <3> DEFINE cc == HandlePromiseSettle(nested, doc, t)
            <3> DEFINE aa == P!HandlePromiseSettle(doc, nested, t)
            <3> DEFINE Rs == { r \in SettleReq : r.id /= req.id }
            <3>1. cc.sends = << >>
                    /\ IF aa = {} THEN cc.doc = doc ELSE aa = {cc.doc}
                <4>1. LET u == HandlePromiseSettle(nested, doc, t)
                          v == P!HandlePromiseSettle(doc, nested, t)
                      IN  u.sends = << >>
                          /\ IF v = {} THEN u.doc = doc ELSE v = {u.doc}
                    BY SettleDoc
                <4>2. QED
                    BY <4>1 DEF cc, aa
            <3>2. c = cc
                BY <1>2, <2>4 DEF c, cc, old, nested, HandleTaskFence
            <3>3. \/ /\ req.action.tag = "Create"
                     /\ req.action.req \in CreateReq
                  \/ /\ req.action.tag = "Settle"
                     /\ req.action.req \in SettleReq
                BY FenceKind
            <3>3b. nested \in SettleReq
                BY <2>4, <3>3 DEF nested
            <3>4. nested \in Rs
                BY <2>4, <3>3b DEF nested, Rs
            <3>5. CASE aa = {}
                BY <3>1, <3>2, <3>5 DEF cc
            <3>6. CASE aa # {}
                <4>1. aa = {cc.doc}
                    BY <3>1, <3>6
                <4>2. cc.doc \in aa
                    BY <4>1
                <4>3. cc.doc \in P!Flat({ P!HandlePromiseSettle(doc, q, t) : q \in Rs })
                    BY <3>4, <4>2, SettleIn DEF aa
                <4>4. a = P!Flat({ P!HandlePromiseCreate(doc, q, t) :
                                     q \in { r \in CreateReq : r.id /= req.id } })
                        \cup P!Flat({ P!HandlePromiseSettle(doc, q, t) : q \in Rs })
                    BY <1>2, <2>1, <2>4, SameCreate, SameSettle
                       DEF a, old, Rs, SameCreate, SameSettle, P!HandleTaskFence
                <4>5. cc.doc \in a
                    BY <4>3, <4>4
                <4>6. QED
                    BY <3>1, <3>2, <4>5 DEF cc
            <3>7. QED
                BY <3>5, <3>6
        <2>5. QED
            BY <2>2, <2>3, <2>4, FenceKind DEF nested
    <1>3. QED
        BY <1>1, <1>2

===============================================================================
