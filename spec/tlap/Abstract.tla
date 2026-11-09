----------------------------- MODULE Abstract -----------------------------
(* The protocol as direct actions. There is no sweep closure: each timeout,
   callback, listener, or request is one transition. *)
EXTENDS Requests

(* Pure request handlers shared by the swept and direct abstract machines.
   A handler returns the object maps it can produce, or the empty set when
   disabled. It does not update either machine's message variable. *)

(* @type: ($object, Int) => $object; *)
New(req, t) ==
    IF req.timeoutAt > t THEN
        [ promise |-> [ state |-> "pending", param |-> req.param, value |-> NoValue,
                        tags |-> req.tags,
                        timeoutAt |-> req.timeoutAt, createdAt |-> t,
                        settledAt |-> NoTime,
                        callbacks |-> {}, listeners |-> {} ],
          task    |-> IF req.tags.targeted THEN
                          [NoTask EXCEPT !.state = "pending", !.retryTimeoutAt = t]
                      ELSE
                          NoTask ]
    ELSE
        [ promise |-> [ state |-> IF req.tags.timer THEN "resolved"
                                                    ELSE "rejectedTimedout",
                        param |-> req.param, value |-> NoValue, tags |-> req.tags,
                        timeoutAt |-> req.timeoutAt, createdAt |-> req.timeoutAt,
                        settledAt |-> req.timeoutAt,
                        callbacks |-> {}, listeners |-> {} ],
          task    |-> IF req.tags.targeted THEN
                          [NoTask EXCEPT !.state = "fulfilled"]
                      ELSE
                          NoTask ]

Project(obj, t) ==
    IF obj.promise.state = "pending" /\ obj.promise.timeoutAt <= t THEN
        [ promise |-> [obj.promise EXCEPT
                          !.state     = IF obj.promise.tags.timer THEN "resolved"
                                        ELSE "rejectedTimedout",
                          !.value     = NoValue,
                          !.settledAt = obj.promise.timeoutAt],
          task    |-> [obj.task EXCEPT !.state          = IF @ = "none" THEN "none"
                                                          ELSE "fulfilled",
                                       !.pid            = NoPid,
                                       !.ttl            = NoTime,
                                       !.leaseTimeoutAt = NoTime,
                                       !.retryTimeoutAt = NoTime,
                                       !.resumes        = {}] ]
    ELSE
        obj

(* TLC rejects `UNION` of the empty set. A fence on the only id has no other
   request to nest, and a disabled handler contributes nothing. *)
Flat(S) ==
    IF S = {} THEN {} ELSE UNION S

-----------------------------------------------------------------------------

HandlePromiseCreate(o, req, t) ==
    IF req.id \in DOMAIN o THEN
        {}
    ELSE
        {Write(o, req.id, New(req, t))}

HandlePromiseSettle(o, req, t) ==
    IF req.id \notin DOMAIN o THEN
        {}
    ELSE
        LET old == Project(o[req.id], t)
            new == [ promise |-> [old.promise EXCEPT !.state     = req.state,
                                                    !.value     = req.value,
                                                    !.settledAt = t],
                     task    |-> [old.task EXCEPT
                                     !.state          = IF @ = "none" THEN "none"
                                                        ELSE "fulfilled",
                                     !.pid            = NoPid,
                                     !.ttl            = NoTime,
                                     !.leaseTimeoutAt = NoTime,
                                     !.retryTimeoutAt = NoTime,
                                     !.resumes        = {}] ]
        IN  IF old.promise.state = "pending" THEN {Write(o, req.id, new)} ELSE {}

HandlePromiseRegisterCallback(o, req, t) ==
    IF req.awaited \notin DOMAIN o \/ req.awaiter \notin DOMAIN o THEN
        {}
    ELSE
        LET awaited == Project(o[req.awaited], t)
            awaiter == Project(o[req.awaiter], t)
        IN  IF /\ awaiter.promise.tags.targeted
               /\ IsExternal(awaited.promise)
               /\ awaited.promise.state = "pending"
               /\ awaiter.promise.state = "pending"
            THEN {Write(o, req.awaited, [awaited EXCEPT !.promise.callbacks = @ \cup {req.awaiter}])}
            ELSE {}

HandlePromiseRegisterListener(o, req, t) ==
    IF req.awaited \notin DOMAIN o THEN
        {}
    ELSE
        LET old == Project(o[req.awaited], t)
        IN  IF IsExternal(old.promise) /\ old.promise.state = "pending"
            THEN {Write(o, req.awaited, [old EXCEPT !.promise.listeners = @ \cup {req.address}])}
            ELSE {}

-----------------------------------------------------------------------------

HandleTaskCreate(o, req, t) ==
    IF ~req.action.tags.targeted THEN
        {}
    ELSE IF req.action.id \notin DOMAIN o THEN
        LET born == New(req.action, t)
            held == [born EXCEPT !.task.state          = "acquired",
                                 !.task.version        = @ + 1,
                                 !.task.ttl            = req.ttl,
                                 !.task.pid            = req.pid,
                                 !.task.leaseTimeoutAt = t + req.ttl,
                                 !.task.retryTimeoutAt = NoTime,
                                 !.task.resumes        = {}]
        IN  {Write(o, req.action.id, IF born.promise.state = "pending" THEN held ELSE born)}
    ELSE
        LET old == Project(o[req.action.id], t)
        IN  IF old.promise.tags.targeted /\ old.task.state = "pending"
            THEN {Write(o, req.action.id,
                        [old EXCEPT !.task.state          = "acquired",
                                    !.task.version        = @ + 1,
                                    !.task.ttl            = req.ttl,
                                    !.task.pid            = req.pid,
                                    !.task.leaseTimeoutAt = t + req.ttl,
                                    !.task.retryTimeoutAt = NoTime,
                                    !.task.resumes        = {}])}
            ELSE {}

HandleTaskAcquire(o, req, t) ==
    IF req.id \notin DOMAIN o THEN
        {}
    ELSE
        LET old == Project(o[req.id], t)
        IN  IF /\ old.task.state = "pending"
               /\ old.promise.state = "pending"
               /\ old.task.version = req.version
            THEN {Write(o, req.id,
                        [old EXCEPT !.task.state          = "acquired",
                                    !.task.version        = @ + 1,
                                    !.task.ttl            = req.ttl,
                                    !.task.pid            = req.pid,
                                    !.task.leaseTimeoutAt = t + req.ttl,
                                    !.task.retryTimeoutAt = NoTime,
                                    !.task.resumes        = {}])}
            ELSE {}

(* The nested create or settle sees this store. It is not projected again. *)
HandleTaskFence(o, i, v, t) ==
    IF i \notin DOMAIN o THEN
        {}
    ELSE
        LET old == Project(o[i], t)
        IN  IF /\ old.task.state = "acquired"
               /\ old.promise.state = "pending"
               /\ old.task.version = v
            THEN
                Flat({HandlePromiseCreate(o, req, t) : req \in {r \in CreateReq : r.id /= i}})
                \cup Flat({HandlePromiseSettle(o, req, t) : req \in {r \in SettleReq : r.id /= i}})
            ELSE
                {}

(* The whole beat, and also the beat of a single origin. The executor
   writes one document, so a heartbeat names one origin's tasks. *)
HandleTaskHeartbeat(o, req, t) ==
    LET beat == { i \in DOMAIN o :
                    LET old == Project(o[i], t)
                    IN  /\ \E rf \in req.tasks :
                              rf.id = i /\ rf.version = old.task.version
                        /\ old.task.state = "acquired"
                        /\ old.task.pid = req.pid
                        /\ old.promise.state = "pending" }
        upd(i) == LET old == Project(o[i], t)
                  IN  [old EXCEPT !.task.leaseTimeoutAt = t + old.task.ttl]
        at(keep) == [ i \in DOMAIN o |-> IF i \in keep THEN upd(i) ELSE o[i] ]
    IN  IF beat = {} THEN
            {}
        ELSE
            {at(beat)} \cup { at({ j \in beat : j.origin = p }) : p \in Origin }

HandleTaskSuspend(o, req, t) ==
    LET aw == {a.awaited : a \in req.actions}
    IN  IF \/ req.actions = {}
           \/ req.id \in aw
           \/ \E a \in aw : a.origin /= req.id.origin
           \/ req.id \notin DOMAIN o
           \/ \E a \in aw : a \notin DOMAIN o
        THEN
            {}
        ELSE
            LET old == Project(o[req.id], t)
            IN  IF \/ old.task.state /= "acquired"
                   \/ old.promise.state /= "pending"
                   \/ old.task.version /= req.version
                   \/ \E a \in aw : ~IsExternal(Project(o[a], t).promise)
                THEN
                    {}
                ELSE IF \E a \in aw : Project(o[a], t).promise.state /= "pending" THEN
                    {Write(o, req.id, [old EXCEPT !.task.resumes = {}])}
                ELSE
                    {[ i \in DOMAIN o |->
                         IF i = req.id THEN
                             [old EXCEPT !.task.state          = "suspended",
                                         !.task.pid            = NoPid,
                                         !.task.ttl            = NoTime,
                                         !.task.leaseTimeoutAt = NoTime,
                                         !.task.retryTimeoutAt = NoTime,
                                         !.task.resumes        = {}]
                         ELSE IF i \in aw THEN
                             [Project(o[i], t) EXCEPT !.promise.callbacks = @ \cup {req.id}]
                         ELSE
                             o[i] ]}

HandleTaskFulfill(o, req, t) ==
    IF req.id \notin DOMAIN o THEN
        {}
    ELSE
        LET old == Project(o[req.id], t)
            new == [ promise |-> [old.promise EXCEPT !.state     = req.action.state,
                                                    !.value     = req.action.value,
                                                    !.settledAt = t],
                     task    |-> [old.task EXCEPT !.state          = "fulfilled",
                                                  !.pid            = NoPid,
                                                  !.ttl            = NoTime,
                                                  !.leaseTimeoutAt = NoTime,
                                                  !.retryTimeoutAt = NoTime,
                                                  !.resumes        = {}] ]
        IN  IF /\ old.task.state = "acquired"
               /\ old.promise.state = "pending"
               /\ old.task.version = req.version
            THEN {Write(o, req.id, new)}
            ELSE {}

HandleTaskRelease(o, req, t) ==
    IF req.id \notin DOMAIN o THEN
        {}
    ELSE
        LET old == Project(o[req.id], t)
        IN  IF /\ old.task.state = "acquired"
               /\ old.promise.state = "pending"
               /\ old.task.version = req.version
            THEN {Write(o, req.id,
                        [old EXCEPT !.task.state          = "pending",
                                    !.task.pid            = NoPid,
                                    !.task.ttl            = NoTime,
                                    !.task.leaseTimeoutAt = NoTime,
                                    !.task.retryTimeoutAt = t])}
            ELSE {}

HandleTaskHalt(o, req, t) ==
    IF req.id \notin DOMAIN o THEN
        {}
    ELSE
        LET old == Project(o[req.id], t)
        IN  IF old.task.state \notin {"none", "fulfilled", "halted"}
            THEN {Write(o, req.id,
                        [old EXCEPT !.task.state          = "halted",
                                    !.task.pid            = NoPid,
                                    !.task.ttl            = NoTime,
                                    !.task.leaseTimeoutAt = NoTime,
                                    !.task.retryTimeoutAt = NoTime])}
            ELSE {}

HandleTaskContinue(o, req, t) ==
    IF req.id \notin DOMAIN o THEN
        {}
    ELSE
        LET old == Project(o[req.id], t)
        IN  IF old.task.state = "halted" /\ old.promise.state = "pending"
            THEN {Write(o, req.id,
                        [old EXCEPT !.task.state          = "pending",
                                    !.task.pid            = NoPid,
                                    !.task.ttl            = NoTime,
                                    !.task.leaseTimeoutAt = NoTime,
                                    !.task.retryTimeoutAt = t])}
            ELSE {}

VARIABLES
    objects,    \* partial: DOMAIN is what exists
    network,    \* at most one entry per MsgKey
    now

vars ==
    <<objects, network, now>>

-----------------------------------------------------------------------------
(* Helpers used only by direct callback and listener actions. *)

WithoutListeners(obj, G) ==
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

WithoutCallbacks(obj, G) ==
    [ promise |-> [ state     |-> obj.promise.state,
                    param     |-> obj.promise.param,
                    value     |-> obj.promise.value,
                    tags      |-> obj.promise.tags,
                    timeoutAt |-> obj.promise.timeoutAt,
                    createdAt |-> obj.promise.createdAt,
                    settledAt |-> obj.promise.settledAt,
                    callbacks |-> obj.promise.callbacks \ G,
                    listeners |-> obj.promise.listeners ],
      task    |-> obj.task ]

WakeSuspended(obj, src, t) ==
    [ promise |-> obj.promise,
      task    |-> [ state          |-> "pending",
                    version        |-> obj.task.version,
                    ttl            |-> NoTime,
                    pid            |-> NoPid,
                    leaseTimeoutAt |-> NoTime,
                    retryTimeoutAt |-> t,
                    resumes        |-> src ] ]

UnionResumes(obj, R) ==
    [ promise |-> obj.promise,
      task    |-> [ state          |-> obj.task.state,
                    version        |-> obj.task.version,
                    ttl            |-> obj.task.ttl,
                    pid            |-> obj.task.pid,
                    leaseTimeoutAt |-> obj.task.leaseTimeoutAt,
                    retryTimeoutAt |-> obj.task.retryTimeoutAt,
                    resumes        |-> obj.task.resumes \cup R ] ]

CallbackObjects(o, awaitedId, awaiterId, t) ==
    LET awaited    == Project(o[awaitedId], t)
        newAwaited == WithoutCallbacks(awaited, {awaiterId})
        struck     == Write(o, awaitedId, newAwaited)
    IN  IF awaiterId \notin DOMAIN o THEN
            struck
        ELSE
            LET awaiter == Project(struck[awaiterId], t)
            IN  IF awaiter.task.state \in {"none", "fulfilled"} THEN
                    Write(struck, awaiterId, awaiter)
                ELSE IF awaiter.task.state = "suspended" THEN
                    Write(struck, awaiterId,
                          WakeSuspended(awaiter, {awaitedId}, t))
                ELSE
                    Write(struck, awaiterId,
                          UnionResumes(awaiter, {awaitedId}))

NetworkWrite(n, msg) ==
    { kept \in n : MsgKey(kept) /= MsgKey(msg) } \cup {msg}

At(t) ==
    t \in 0 .. now

Store(os) ==
    /\ objects' = os
    /\ UNCHANGED <<network, now>>

-----------------------------------------------------------------------------
(* Direct internal actions. Promise, lease, and callback processing never
   writes the network. Retry and listener processing may either write their
   message or lose it, while still consuming/rearming the obligation. *)

PromiseTimeout(id, t) ==
    /\ At(t)
    /\ id \in DOMAIN objects
    /\ objects[id].promise.state = "pending"
    /\ objects[id].promise.timeoutAt <= t
    /\ objects' = Write(objects, id, Project(objects[id], t))
    /\ UNCHANGED <<network, now>>

LeaseTimeout(id, t) ==
    /\ At(t)
    /\ id \in DOMAIN objects
    /\ LET old == objects[id]
       IN  /\ old.task.state = "acquired"
           /\ old.task.leaseTimeoutAt /= NoTime
           /\ old.task.leaseTimeoutAt <= t
           /\ Project(old, t).promise.state = "pending"
           /\ objects' =
                Write(objects, id,
                      [old EXCEPT !.task.state          = "pending",
                                  !.task.pid            = NoPid,
                                  !.task.ttl            = NoTime,
                                  !.task.leaseTimeoutAt = NoTime,
                                  !.task.retryTimeoutAt = t])
    /\ UNCHANGED <<network, now>>

RetryTimeout(id, t) ==
    /\ At(t)
    /\ id \in DOMAIN objects
    /\ LET old == objects[id]
           msg == [ address |-> old.promise.tags.target,
                    message |-> [ tag     |-> "Execute",
                                  id      |-> id,
                                  version |-> old.task.version ] ]
       IN  /\ old.task.state = "pending"
           /\ old.task.retryTimeoutAt /= NoTime
           /\ old.task.retryTimeoutAt <= t
           /\ Project(old, t).promise.state = "pending"
           /\ objects' =
                Write(objects, id,
                      [old EXCEPT
                          !.task.retryTimeoutAt = t + RetryDelay])
           /\ network' \in {network, NetworkWrite(network, msg)}
    /\ UNCHANGED now

ProcessCallback(awaited, awaiter, t) ==
    /\ At(t)
    /\ awaited \in DOMAIN objects
    /\ awaiter \in objects[awaited].promise.callbacks
    /\ Project(objects[awaited], t).promise.state /= "pending"
    /\ objects' = CallbackObjects(objects, awaited, awaiter, t)
    /\ UNCHANGED <<network, now>>

(* There is deliberately no decision-time parameter. A listener is eligible
   only after its promise is already stored as settled. *)
ProcessListener(id, address) ==
    /\ id \in DOMAIN objects
    /\ address \in objects[id].promise.listeners
    /\ objects[id].promise.state /= "pending"
    /\ LET awaited == objects[id]
           msg     == [ address |-> address,
                        message |-> [ tag   |-> "Unblock",
                                      id    |-> id,
                                      state |-> awaited.promise.state ] ]
       IN  /\ objects' =
                    Write(objects, id,
                          WithoutListeners(awaited, {address}))
           /\ network' \in {network, NetworkWrite(network, msg)}
    /\ UNCHANGED now

-----------------------------------------------------------------------------
(* Direct request actions. A disabled handler disables the corresponding
   action; [][Next]_vars still admits protocol stuttering. *)

PromiseCreate(req, t) ==
    /\ At(t)
    /\ \E os \in HandlePromiseCreate(objects, req, t) : Store(os)

PromiseSettle(req, t) ==
    /\ At(t)
    /\ \E os \in HandlePromiseSettle(objects, req, t) : Store(os)

PromiseRegisterCallback(req, t) ==
    /\ At(t)
    /\ \E os \in HandlePromiseRegisterCallback(objects, req, t) : Store(os)

PromiseRegisterListener(req, t) ==
    /\ At(t)
    /\ \E os \in HandlePromiseRegisterListener(objects, req, t) : Store(os)

TaskCreate(req, t) ==
    /\ At(t)
    /\ \E os \in HandleTaskCreate(objects, req, t) : Store(os)

TaskAcquire(req, t) ==
    /\ At(t)
    /\ \E os \in HandleTaskAcquire(objects, req, t) : Store(os)

TaskFence(id, version, t) ==
    /\ At(t)
    /\ \E os \in HandleTaskFence(objects, id, version, t) : Store(os)

TaskHeartbeat(req, t) ==
    /\ At(t)
    /\ \E os \in HandleTaskHeartbeat(objects, req, t) : Store(os)

TaskSuspend(req, t) ==
    /\ At(t)
    /\ \E os \in HandleTaskSuspend(objects, req, t) : Store(os)

TaskFulfill(req, t) ==
    /\ At(t)
    /\ \E os \in HandleTaskFulfill(objects, req, t) : Store(os)

TaskRelease(req, t) ==
    /\ At(t)
    /\ \E os \in HandleTaskRelease(objects, req, t) : Store(os)

TaskHalt(req, t) ==
    /\ At(t)
    /\ \E os \in HandleTaskHalt(objects, req, t) : Store(os)

TaskContinue(req, t) ==
    /\ At(t)
    /\ \E os \in HandleTaskContinue(objects, req, t) : Store(os)

Clock ==
    /\ now' = now + 1
    /\ UNCHANGED <<objects, network>>

-----------------------------------------------------------------------------

Init ==
    /\ objects = EmptyFn
    /\ network = {}
    /\ now = 0

AnyPromiseTimeout ==
    \E id \in Id, t \in 0 .. now : PromiseTimeout(id, t)

AnyLeaseTimeout ==
    \E id \in Id, t \in 0 .. now : LeaseTimeout(id, t)

AnyRetryTimeout ==
    \E id \in Id, t \in 0 .. now : RetryTimeout(id, t)

AnyCallback ==
    \E awaited, awaiter \in Id, t \in 0 .. now :
        ProcessCallback(awaited, awaiter, t)

AnyListener ==
    \E id \in Id, address \in Address : ProcessListener(id, address)

Next ==
    \/ AnyPromiseTimeout
    \/ AnyLeaseTimeout
    \/ AnyRetryTimeout
    \/ AnyCallback
    \/ AnyListener
    \/ \E req \in CreateReq, t \in 0 .. now :
          PromiseCreate(req, t)
    \/ \E req \in SettleReq, t \in 0 .. now :
          PromiseSettle(req, t)
    \/ \E req \in CallbackReq, t \in 0 .. now :
          PromiseRegisterCallback(req, t)
    \/ \E req \in [awaited : Id, address : Address], t \in 0 .. now :
          PromiseRegisterListener(req, t)
    \/ \E req \in [pid : Pid, ttl : Ttl, action : CreateReq],
          t \in 0 .. now :
          TaskCreate(req, t)
    \/ \E req \in [id : Id, version : Version, pid : Pid, ttl : Ttl],
          t \in 0 .. now :
          TaskAcquire(req, t)
    \/ \E id \in Id, version \in Version, t \in 0 .. now :
          TaskFence(id, version, t)
    \/ \E req \in [pid : Pid, tasks : SUBSET TaskRefT],
          t \in 0 .. now :
          TaskHeartbeat(req, t)
    \/ \E req \in [id : Id, version : Version,
                    actions : SUBSET CallbackReq],
          t \in 0 .. now :
          TaskSuspend(req, t)
    \/ \E req \in [id : Id, version : Version, action : SettleReq],
          t \in 0 .. now :
          TaskFulfill(req, t)
    \/ \E req \in TaskRefT, t \in 0 .. now :
          TaskRelease(req, t)
    \/ \E req \in [id : Id], t \in 0 .. now :
          TaskHalt(req, t)
    \/ \E req \in [id : Id], t \in 0 .. now :
          TaskContinue(req, t)
    \/ Clock

Fairness ==
    /\ WF_vars(AnyPromiseTimeout)
    /\ WF_vars(AnyLeaseTimeout)
    /\ WF_vars(AnyRetryTimeout)
    /\ WF_vars(AnyCallback)
    /\ WF_vars(AnyListener)
    /\ WF_vars(Clock)

Spec ==
    Init /\ [][Next]_vars /\ Fairness

Safety ==
    Init /\ [][Next]_vars

-----------------------------------------------------------------------------

NowBound ==
    now <= MaxTime

VersionBound ==
    \A id \in DOMAIN objects :
        objects[id].task.version <= MaxVersion

TypeOK ==
    /\ now \in Time
    /\ DOMAIN objects \subseteq Id
    /\ \A id \in DOMAIN objects : objects[id] \in Object
    /\ network \subseteq OutEntry
    /\ \A a, b \in network : MsgKey(a) = MsgKey(b) => a = b

UnitCoherent ==
    \A id \in DOMAIN objects :
        (/\ objects[id].promise.state /= "pending"
         /\ objects[id].task.state \notin {"none", "fulfilled"})
            => FALSE

=============================================================================
