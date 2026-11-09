----------------------------- MODULE Abstract -----------------------------
(* The protocol as direct actions. There is no sweep closure: each timeout,
   callback, listener, or request is one transition. *)
EXTENDS AbstractHandlers

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
