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
HandleTaskFence(o, req, t) ==
    IF req.id \notin DOMAIN o THEN
        {}
    ELSE
        LET old == Project(o[req.id], t)
        IN  IF /\ req.action.req.id /= req.id
               /\ req.action.req.id.origin = req.id.origin
               /\ old.task.state = "acquired"
               /\ old.promise.state = "pending"
               /\ old.task.version = req.version
            THEN
                IF req.action.tag = "Create"
                THEN HandlePromiseCreate(o, req.action.req, t)
                ELSE HandlePromiseSettle(o, req.action.req, t)
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

CallbackObjects(o, awaitedId, awaiterId) ==
    LET awaited    == Project(o[awaitedId], now)
        newAwaited == WithoutCallbacks(awaited, {awaiterId})
        struck     == Write(o, awaitedId, newAwaited)
    IN  IF awaiterId \notin DOMAIN o THEN
            struck
        ELSE
            LET awaiter == Project(struck[awaiterId], now)
            IN  IF awaiter.task.state \in {"none", "fulfilled"} THEN
                    Write(struck, awaiterId, awaiter)
                ELSE IF awaiter.task.state = "suspended" THEN
                    Write(struck, awaiterId,
                          WakeSuspended(awaiter, {awaitedId}, now))
                ELSE
                    Write(struck, awaiterId,
                          UnionResumes(awaiter, {awaitedId}))

NetworkWrite(n, msg) ==
    { kept \in n : MsgKey(kept) /= MsgKey(msg) } \cup {msg}

NetworkWrites(n, messages) ==
    { kept \in n :
        \A msg \in messages : MsgKey(kept) /= MsgKey(msg) } \cup messages

BatchState(o, n) ==
    [objects |-> o, network |-> n]

(* Each batch stage is a pure transformer over an explicit store/network
   record. Eligibility is recomputed between categories, at the current
   protocol time. A category may contribute nothing, but a Batch as a whole
   must select at least one internal item. *)

PromiseTimeoutItems(o, t) ==
    { id \in DOMAIN o :
        /\ o[id].promise.state = "pending"
        /\ o[id].promise.timeoutAt <= t }

ApplyPromiseTimeouts(stage, chosen, t) ==
    BatchState(
        [ id \in DOMAIN stage.objects |->
            IF id \in chosen
            THEN Project(stage.objects[id], t)
            ELSE stage.objects[id] ],
        stage.network)

ListenerItems(o) ==
    { item \in [id : DOMAIN o, address : Address] :
        /\ item.address \in o[item.id].promise.listeners
        /\ o[item.id].promise.state /= "pending" }

ListenerMessage(o, item) ==
    [ address |-> item.address,
      message |-> [ tag   |-> "Unblock",
                    id    |-> item.id,
                    state |-> o[item.id].promise.state ] ]

ApplyListeners(stage, chosen, emitted) ==
    LET messages == { ListenerMessage(stage.objects, item) :
                        item \in emitted }
    IN
        BatchState(
            [ id \in DOMAIN stage.objects |->
                LET addresses ==
                        { item.address :
                            item \in { x \in chosen : x.id = id } }
                IN  IF addresses = {}
                    THEN stage.objects[id]
                    ELSE WithoutListeners(stage.objects[id], addresses) ],
            NetworkWrites(stage.network, messages))

CallbackItems(o, t) ==
    { item \in [awaited : DOMAIN o, awaiter : Id] :
        /\ item.awaiter \in o[item.awaited].promise.callbacks
        /\ Project(o[item.awaited], t).promise.state /= "pending" }

ApplyCallbacks(stage, chosen, t) ==
    LET struck ==
            [ id \in DOMAIN stage.objects |->
                LET awaiters ==
                        { item.awaiter :
                            item \in { x \in chosen : x.awaited = id } }
                IN  IF awaiters = {}
                    THEN stage.objects[id]
                    ELSE WithoutCallbacks(
                            Project(stage.objects[id], t), awaiters) ]
        final ==
            [ id \in DOMAIN struck |->
                LET resumes ==
                        { item.awaited :
                            item \in { x \in chosen : x.awaiter = id } }
                IN  IF resumes = {} THEN
                        struck[id]
                    ELSE
                        LET awaiter == Project(struck[id], t)
                        IN  IF awaiter.task.state \in {"none", "fulfilled"} THEN
                                awaiter
                            ELSE IF awaiter.task.state = "suspended" THEN
                                WakeSuspended(awaiter, resumes, t)
                            ELSE
                                UnionResumes(awaiter, resumes) ]
    IN
        BatchState(final, stage.network)

LeaseTimeoutItems(o, t) ==
    { id \in DOMAIN o :
        LET old == o[id]
        IN  /\ old.task.state = "acquired"
            /\ old.task.leaseTimeoutAt /= NoTime
            /\ old.task.leaseTimeoutAt <= t
            /\ Project(old, t).promise.state = "pending" }

ApplyLeaseTimeouts(stage, chosen, t) ==
    BatchState(
        [ id \in DOMAIN stage.objects |->
            IF id \notin chosen THEN
                stage.objects[id]
            ELSE
                [stage.objects[id] EXCEPT
                    !.task.state          = "pending",
                    !.task.pid            = NoPid,
                    !.task.ttl            = NoTime,
                    !.task.leaseTimeoutAt = NoTime,
                    !.task.retryTimeoutAt = t] ],
        stage.network)

RetryTimeoutItems(o, t) ==
    { id \in DOMAIN o :
        LET old == o[id]
        IN  /\ old.task.state = "pending"
            /\ old.task.retryTimeoutAt /= NoTime
            /\ old.task.retryTimeoutAt <= t
            /\ Project(old, t).promise.state = "pending" }

RetryMessage(o, id) ==
    [ address |-> o[id].promise.tags.target,
      message |-> [ tag     |-> "Execute",
                    id      |-> id,
                    version |-> o[id].task.version ] ]

ApplyRetryTimeouts(stage, chosen, emitted, t) ==
    LET messages == { RetryMessage(stage.objects, id) : id \in emitted }
    IN
        BatchState(
            [ id \in DOMAIN stage.objects |->
                IF id \in chosen
                THEN [stage.objects[id] EXCEPT
                          !.task.retryTimeoutAt = t + RetryDelay]
                ELSE stage.objects[id] ],
            NetworkWrites(stage.network, messages))

(* The event wrapper is removed only where the shared alphabet wraps a
   request in `.req`. In particular TaskFence receives the complete event,
   including its fencing id, version, and nested action. *)
HandleRequest(o, req, t) ==
    CASE req.tag = "PromiseCreate" ->
             HandlePromiseCreate(o, req.req, t)
      [] req.tag = "PromiseSettle" ->
             HandlePromiseSettle(o, req.req, t)
      [] req.tag = "PromiseRegisterCallback" ->
             HandlePromiseRegisterCallback(o, req.req, t)
      [] req.tag = "PromiseRegisterListener" ->
             HandlePromiseRegisterListener(o, req, t)
      [] req.tag = "TaskCreate" ->
             HandleTaskCreate(o, req, t)
      [] req.tag = "TaskAcquire" ->
             HandleTaskAcquire(o, req, t)
      [] req.tag = "TaskFence" ->
             HandleTaskFence(o, req, t)
      [] req.tag = "TaskHeartbeat" ->
             HandleTaskHeartbeat(o, req, t)
      [] req.tag = "TaskSuspend" ->
             HandleTaskSuspend(o, req, t)
      [] req.tag = "TaskFulfill" ->
             HandleTaskFulfill(o, req, t)
      [] req.tag = "TaskRelease" ->
             HandleTaskRelease(o, req, t)
      [] req.tag = "TaskHalt" ->
             HandleTaskHalt(o, req, t)
      [] OTHER ->
             HandleTaskContinue(o, req, t)

OptionalRequest ==
    {{}} \cup { {req} : req \in ExternalEvent }

ApplyRequest(o, chosen, t) ==
    IF chosen = {}
    THEN {o}
    ELSE UNION { HandleRequest(o, req, t) : req \in chosen }

(* A declarative, bounded-by-the-state batch: choose any nonempty collection
   of currently eligible internal items, apply the five categories in the
   executor's order, and then apply zero or one enabled request. Listener and
   retry sends remain best effort. Request-only transitions remain the direct
   actions below. *)
Batch ==
    LET initial == BatchState(objects, network)
    IN  \E promiseItems \in SUBSET PromiseTimeoutItems(initial.objects, now) :
        LET afterPromises ==
                ApplyPromiseTimeouts(initial, promiseItems, now)
        IN  \E listenerItems \in SUBSET ListenerItems(afterPromises.objects) :
            \E emittedListeners \in SUBSET listenerItems :
            LET afterListeners ==
                    ApplyListeners(
                        afterPromises, listenerItems, emittedListeners)
            IN  \E callbackItems \in
                        SUBSET CallbackItems(afterListeners.objects, now) :
                LET afterCallbacks ==
                        ApplyCallbacks(afterListeners, callbackItems, now)
                IN  \E leaseItems \in
                            SUBSET LeaseTimeoutItems(
                                afterCallbacks.objects, now) :
                    LET afterLeases ==
                            ApplyLeaseTimeouts(
                                afterCallbacks, leaseItems, now)
                    IN  \E retryItems \in
                                SUBSET RetryTimeoutItems(
                                    afterLeases.objects, now) :
                        \E emittedRetries \in SUBSET retryItems :
                        LET afterRetries ==
                                ApplyRetryTimeouts(
                                    afterLeases, retryItems,
                                    emittedRetries, now)
                        IN  /\ \/ promiseItems /= {}
                                  \/ listenerItems /= {}
                                  \/ callbackItems /= {}
                                  \/ leaseItems /= {}
                                  \/ retryItems /= {}
                            /\ \E request \in OptionalRequest :
                                \E finalObjects \in
                                        ApplyRequest(
                                            afterRetries.objects,
                                            request, now) :
                                    /\ objects' = finalObjects
                                    /\ network' = afterRetries.network
                                    /\ UNCHANGED now

Store(os) ==
    /\ objects' = os
    /\ UNCHANGED <<network, now>>

-----------------------------------------------------------------------------
(* Direct internal actions. Promise, lease, and callback processing never
   writes the network. Retry and listener processing may either write their
   message or lose it, while still consuming/rearming the obligation. *)

PromiseTimeout(id) ==
    /\ id \in DOMAIN objects
    /\ objects[id].promise.state = "pending"
    /\ objects[id].promise.timeoutAt <= now
    /\ objects' = Write(objects, id, Project(objects[id], now))
    /\ UNCHANGED <<network, now>>

LeaseTimeout(id) ==
    /\ id \in DOMAIN objects
    /\ LET old == objects[id]
       IN  /\ old.task.state = "acquired"
           /\ old.task.leaseTimeoutAt /= NoTime
           /\ old.task.leaseTimeoutAt <= now
           /\ Project(old, now).promise.state = "pending"
           /\ objects' =
                Write(objects, id,
                      [old EXCEPT !.task.state          = "pending",
                                  !.task.pid            = NoPid,
                                  !.task.ttl            = NoTime,
                                  !.task.leaseTimeoutAt = NoTime,
                                  !.task.retryTimeoutAt = now])
    /\ UNCHANGED <<network, now>>

RetryTimeout(id) ==
    /\ id \in DOMAIN objects
    /\ LET old == objects[id]
           msg == [ address |-> old.promise.tags.target,
                    message |-> [ tag     |-> "Execute",
                                  id      |-> id,
                                  version |-> old.task.version ] ]
       IN  /\ old.task.state = "pending"
           /\ old.task.retryTimeoutAt /= NoTime
           /\ old.task.retryTimeoutAt <= now
           /\ Project(old, now).promise.state = "pending"
           /\ objects' =
                Write(objects, id,
                      [old EXCEPT
                          !.task.retryTimeoutAt = now + RetryDelay])
           /\ network' \in {network, NetworkWrite(network, msg)}
    /\ UNCHANGED now

ProcessCallback(awaited, awaiter) ==
    /\ awaited \in DOMAIN objects
    /\ awaiter \in objects[awaited].promise.callbacks
    /\ Project(objects[awaited], now).promise.state /= "pending"
    /\ objects' = CallbackObjects(objects, awaited, awaiter)
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

PromiseCreate(req) ==
    \E os \in HandlePromiseCreate(objects, req, now) : Store(os)

PromiseSettle(req) ==
    \E os \in HandlePromiseSettle(objects, req, now) : Store(os)

PromiseRegisterCallback(req) ==
    \E os \in HandlePromiseRegisterCallback(objects, req, now) : Store(os)

PromiseRegisterListener(req) ==
    \E os \in HandlePromiseRegisterListener(objects, req, now) : Store(os)

TaskCreate(req) ==
    \E os \in HandleTaskCreate(objects, req, now) : Store(os)

TaskAcquire(req) ==
    \E os \in HandleTaskAcquire(objects, req, now) : Store(os)

TaskFence(req) ==
    \E os \in HandleTaskFence(objects, req, now) : Store(os)

TaskHeartbeat(req) ==
    \E os \in HandleTaskHeartbeat(objects, req, now) : Store(os)

TaskSuspend(req) ==
    \E os \in HandleTaskSuspend(objects, req, now) : Store(os)

TaskFulfill(req) ==
    \E os \in HandleTaskFulfill(objects, req, now) : Store(os)

TaskRelease(req) ==
    \E os \in HandleTaskRelease(objects, req, now) : Store(os)

TaskHalt(req) ==
    \E os \in HandleTaskHalt(objects, req, now) : Store(os)

TaskContinue(req) ==
    \E os \in HandleTaskContinue(objects, req, now) : Store(os)

Clock ==
    /\ now' = now + 1
    /\ UNCHANGED <<objects, network>>

-----------------------------------------------------------------------------

Init ==
    /\ objects = EmptyFn
    /\ network = {}
    /\ now = 0

AnyPromiseTimeout ==
    \E id \in Id : PromiseTimeout(id)

AnyLeaseTimeout ==
    \E id \in Id : LeaseTimeout(id)

AnyRetryTimeout ==
    \E id \in Id : RetryTimeout(id)

AnyCallback ==
    \E awaited, awaiter \in Id :
        ProcessCallback(awaited, awaiter)

AnyListener ==
    \E id \in Id, address \in Address : ProcessListener(id, address)

Next ==
    \/ Batch
    \/ AnyPromiseTimeout
    \/ AnyLeaseTimeout
    \/ AnyRetryTimeout
    \/ AnyCallback
    \/ AnyListener
    \/ \E req \in CreateReq : PromiseCreate(req)
    \/ \E req \in SettleReq : PromiseSettle(req)
    \/ \E req \in CallbackReq : PromiseRegisterCallback(req)
    \/ \E req \in [awaited : Id, address : Address] :
          PromiseRegisterListener(req)
    \/ \E req \in [pid : Pid, ttl : Ttl, action : CreateReq] :
          TaskCreate(req)
    \/ \E req \in [id : Id, version : Version, pid : Pid, ttl : Ttl] :
          TaskAcquire(req)
    \/ \E req \in [id : Id, version : Version, action : FenceAction] :
          TaskFence(req)
    \/ \E req \in [pid : Pid, tasks : SUBSET TaskRefT] :
          TaskHeartbeat(req)
    \/ \E req \in [id : Id, version : Version,
                    actions : SUBSET CallbackReq] :
          TaskSuspend(req)
    \/ \E req \in [id : Id, version : Version, action : SettleReq] :
          TaskFulfill(req)
    \/ \E req \in TaskRefT : TaskRelease(req)
    \/ \E req \in [id : Id] : TaskHalt(req)
    \/ \E req \in [id : Id] : TaskContinue(req)
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
