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
    network     \* at most one entry per MsgKey

vars ==
    <<objects, network>>

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

CallbackObjects(o, awaitedId, awaiterId, at) ==
    LET awaited    == Project(o[awaitedId], at)
        newAwaited == WithoutCallbacks(awaited, {awaiterId})
        struck     == Write(o, awaitedId, newAwaited)
    IN  IF awaiterId \notin DOMAIN o THEN
            struck
        ELSE
            LET awaiter == Project(struck[awaiterId], at)
            IN  IF awaiter.task.state \in {"none", "fulfilled"} THEN
                    Write(struck, awaiterId, awaiter)
                ELSE IF awaiter.task.state = "suspended" THEN
                    Write(struck, awaiterId,
                          WakeSuspended(awaiter, {awaitedId}, at))
                ELSE
                    Write(struck, awaiterId,
                          UnionResumes(awaiter, {awaitedId}))

NetworkWrite(n, msg) ==
    { kept \in n : MsgKey(kept) /= MsgKey(msg) } \cup {msg}

BatchState(os, net) ==
    [objects |-> os, network |-> net]

CurrentBatchState ==
    BatchState(objects, network)

NetworkWrites(net, messages) ==
    { old \in net :
        \A msg \in messages : MsgKey(old) /= MsgKey(msg) } \cup messages

-----------------------------------------------------------------------------
(* Stage 1: promise timeouts. *)

EligiblePromises(st, t) ==
    { id \in DOMAIN st.objects :
        /\ st.objects[id].promise.state = "pending"
        /\ st.objects[id].promise.timeoutAt <= t }

ApplyPromises(st, picked, t) ==
    BatchState(
        [id \in DOMAIN st.objects |->
            IF id \in picked
            THEN Project(st.objects[id], t)
            ELSE st.objects[id]],
        st.network)

PromiseChoices(st, t) ==
    { [state |-> ApplyPromises(st, picked, t),
       count |-> Cardinality(picked)] :
        picked \in SUBSET EligiblePromises(st, t) }

-----------------------------------------------------------------------------
(* Stage 2: listeners. Sending is best effort, as in ProcessListener. *)

EligibleListeners(st) ==
    { x \in [id : DOMAIN st.objects, address : Address] :
        /\ st.objects[x.id].promise.state /= "pending"
        /\ x.address \in st.objects[x.id].promise.listeners }

ListenerMessage(st, x) ==
    [ address |-> x.address,
      message |-> [ tag   |-> "Unblock",
                    id    |-> x.id,
                    state |-> st.objects[x.id].promise.state ] ]

ApplyListeners(st, picked, sent) ==
    LET Drop(id) ==
            { x.address : x \in { y \in picked : y.id = id } }
        messages == { ListenerMessage(st, x) : x \in sent }
    IN  BatchState(
            [id \in DOMAIN st.objects |->
                IF Drop(id) = {}
                THEN st.objects[id]
                ELSE WithoutListeners(st.objects[id], Drop(id))],
            NetworkWrites(st.network, messages))

ListenerChoices(st) ==
    UNION
      { { [state |-> ApplyListeners(st, picked, sent),
           count |-> Cardinality(picked)] :
            sent \in SUBSET picked } :
        picked \in SUBSET EligibleListeners(st) }

-----------------------------------------------------------------------------
(* Stage 3: callbacks. The bulk image is the endpoint of processing the     *)
(* selected callback edges one at a time in any order. Sources are unioned  *)
(* when several settled promises wake the same task.                        *)

EligibleCallbacks(st, t) ==
    { x \in [awaited : DOMAIN st.objects, awaiter : Id] :
        /\ x.awaiter \in st.objects[x.awaited].promise.callbacks
        /\ Project(st.objects[x.awaited], t).promise.state /= "pending" }

ApplyCallbacks(st, picked, t) ==
    LET Removed(id) ==
            { x.awaiter :
                x \in { y \in picked : y.awaited = id } }
        Struck ==
            [id \in DOMAIN st.objects |->
                IF Removed(id) = {}
                THEN st.objects[id]
                ELSE WithoutCallbacks(Project(st.objects[id], t),
                                      Removed(id))]
        Sources(id) ==
            { x.awaited :
                x \in { y \in picked : y.awaiter = id } }
    IN  BatchState(
            [id \in DOMAIN Struck |->
                IF Sources(id) = {} THEN
                    Struck[id]
                ELSE
                    LET awaiter == Project(Struck[id], t)
                    IN  IF awaiter.task.state \in {"none", "fulfilled"} THEN
                            awaiter
                        ELSE IF awaiter.task.state = "suspended" THEN
                            WakeSuspended(awaiter, Sources(id), t)
                        ELSE
                            UnionResumes(awaiter, Sources(id))],
            st.network)

CallbackChoices(st, t) ==
    { [state |-> ApplyCallbacks(st, picked, t),
       count |-> Cardinality(picked)] :
        picked \in SUBSET EligibleCallbacks(st, t) }

-----------------------------------------------------------------------------
(* Stage 4: expired leases. *)

EligibleLeases(st, t) ==
    { id \in DOMAIN st.objects :
        LET old == st.objects[id]
        IN  /\ old.task.state = "acquired"
            /\ old.task.leaseTimeoutAt /= NoTime
            /\ old.task.leaseTimeoutAt <= t
            /\ Project(old, t).promise.state = "pending" }

ApplyLeases(st, picked, t) ==
    BatchState(
        [id \in DOMAIN st.objects |->
            IF id \notin picked THEN
                st.objects[id]
            ELSE
                [st.objects[id] EXCEPT
                    !.task.state          = "pending",
                    !.task.pid            = NoPid,
                    !.task.ttl            = NoTime,
                    !.task.leaseTimeoutAt = NoTime,
                    !.task.retryTimeoutAt = t]],
        st.network)

LeaseChoices(st, t) ==
    { [state |-> ApplyLeases(st, picked, t),
       count |-> Cardinality(picked)] :
        picked \in SUBSET EligibleLeases(st, t) }

-----------------------------------------------------------------------------
(* Stage 5: retries. Sending is independently best effort for every retry. *)

EligibleRetries(st, t) ==
    { id \in DOMAIN st.objects :
        LET old == st.objects[id]
        IN  /\ old.task.state = "pending"
            /\ old.task.retryTimeoutAt /= NoTime
            /\ old.task.retryTimeoutAt <= t
            /\ Project(old, t).promise.state = "pending" }

RetryMessage(st, id) ==
    [ address |-> st.objects[id].promise.tags.target,
      message |-> [ tag     |-> "Execute",
                    id      |-> id,
                    version |-> st.objects[id].task.version ] ]

ApplyRetries(st, picked, sent, t) ==
    LET messages == { RetryMessage(st, id) : id \in sent }
    IN  BatchState(
            [id \in DOMAIN st.objects |->
                IF id \in picked
                THEN [st.objects[id] EXCEPT
                          !.task.retryTimeoutAt = t + RetryDelay]
                ELSE st.objects[id]],
            NetworkWrites(st.network, messages))

RetryChoices(st, t) ==
    UNION
      { { [state |-> ApplyRetries(st, picked, sent, t),
           count |-> Cardinality(picked)] :
            sent \in SUBSET picked } :
        picked \in SUBSET EligibleRetries(st, t) }

-----------------------------------------------------------------------------
(* Stage 6: at most one request. Disabled handlers have no request choice;  *)
(* the zero-request choice still covers an internal Timeout event or a      *)
(* concrete request whose handler is a document stutter.                    *)

RequestObjects(os, ev, t) ==
    CASE ev.tag = "PromiseCreate" ->
             HandlePromiseCreate(os, ev.req, t)
      [] ev.tag = "PromiseSettle" ->
             HandlePromiseSettle(os, ev.req, t)
      [] ev.tag = "PromiseRegisterCallback" ->
             HandlePromiseRegisterCallback(os, ev.req, t)
      [] ev.tag = "PromiseRegisterListener" ->
             HandlePromiseRegisterListener(os, ev, t)
      [] ev.tag = "TaskCreate" ->
             HandleTaskCreate(os, ev, t)
      [] ev.tag = "TaskAcquire" ->
             HandleTaskAcquire(os, ev, t)
      [] ev.tag = "TaskFence" ->
             HandleTaskFence(os, ev, t)
      [] ev.tag = "TaskHeartbeat" ->
             HandleTaskHeartbeat(os, ev, t)
      [] ev.tag = "TaskSuspend" ->
             HandleTaskSuspend(os, ev, t)
      [] ev.tag = "TaskFulfill" ->
             HandleTaskFulfill(os, ev, t)
      [] ev.tag = "TaskRelease" ->
             HandleTaskRelease(os, ev, t)
      [] ev.tag = "TaskHalt" ->
             HandleTaskHalt(os, ev, t)
      [] ev.tag = "TaskContinue" ->
             HandleTaskContinue(os, ev, t)

RequestChoices(st, t) ==
    { [state |-> st, count |-> 0] }
    \cup
    UNION
      { { [state |-> BatchState(os, st.network), count |-> 1] :
            os \in RequestObjects(st.objects, ev, t) } :
        ev \in ExternalEvent }

-----------------------------------------------------------------------------
(* The fixed-size witness makes category order explicit. states[1] is the   *)
(* input; states[2] through states[7] are promise, listener, callback,       *)
(* lease, retry, and optional-request endpoints.                            *)

PipelineWitnesses(st, t) ==
    UNION
      { UNION
          { UNION
              { UNION
                  { UNION
                      { { [states |->
                                <<st,
                                  p.state,
                                  l.state,
                                  c.state,
                                  e.state,
                                  y.state,
                                  r.state>>,
                           work |-> p.count + l.count + c.count
                                   + e.count + y.count + r.count] :
                            r \in RequestChoices(y.state, t) } :
                        y \in RetryChoices(e.state, t) } :
                    e \in LeaseChoices(c.state, t) } :
                c \in CallbackChoices(l.state, t) } :
            l \in ListenerChoices(p.state) } :
        p \in PromiseChoices(st, t) }

(*
 * Concrete!Sweep's document endpoint is the witness that chooses every
 * eligible item at each successive stage and sends every selected message.
 * Timer puts and deletes are deliberately absent: they are executor index
 * maintenance, not fields of Abstract's protocol state.
 *)
FullSweepWitness(st, t) ==
    LET ps == EligiblePromises(st, t)
        p  == ApplyPromises(st, ps, t)
        ls == EligibleListeners(p)
        l  == ApplyListeners(p, ls, ls)
        cs == EligibleCallbacks(l, t)
        c  == ApplyCallbacks(l, cs, t)
        es == EligibleLeases(c, t)
        e  == ApplyLeases(c, es, t)
        ys == EligibleRetries(e, t)
        y  == ApplyRetries(e, ys, ys, t)
    IN  [states |-> <<st, p, l, c, e, y, y>>,
         work   |-> Cardinality(ps) + Cardinality(ls)
                   + Cardinality(cs) + Cardinality(es)
                   + Cardinality(ys)]

(* Executable sanity check: the all-eligible endpoint is one member of the
   same relation used by Batch (with no request in its final stage). *)
FullSweepAdmitted ==
    \A at \in Horizon :
        FullSweepWitness(CurrentBatchState, at)
            \in PipelineWitnesses(CurrentBatchState, at)

Batch ==
    \E at \in Horizon :
        \E witness \in PipelineWitnesses(CurrentBatchState, at) :
            /\ witness.work > 0
            /\ objects' = witness.states[7].objects
            /\ network' = witness.states[7].network

Store(os) ==
    /\ objects' = os
    /\ UNCHANGED network

-----------------------------------------------------------------------------
(* Direct internal actions. Promise, lease, and callback processing never
   writes the network. Retry and listener processing may either write their
   message or lose it, while still consuming/rearming the obligation. *)

PromiseTimeout(id, at) ==
    /\ id \in DOMAIN objects
    /\ objects[id].promise.state = "pending"
    /\ objects[id].promise.timeoutAt <= at
    /\ objects' = Write(objects, id, Project(objects[id], at))
    /\ UNCHANGED network

LeaseTimeout(id, at) ==
    /\ id \in DOMAIN objects
    /\ LET old == objects[id]
       IN  /\ old.task.state = "acquired"
           /\ old.task.leaseTimeoutAt /= NoTime
           /\ old.task.leaseTimeoutAt <= at
           /\ Project(old, at).promise.state = "pending"
           /\ objects' =
                Write(objects, id,
                      [old EXCEPT !.task.state          = "pending",
                                  !.task.pid            = NoPid,
                                  !.task.ttl            = NoTime,
                                  !.task.leaseTimeoutAt = NoTime,
                                  !.task.retryTimeoutAt = at])
    /\ UNCHANGED network

RetryTimeout(id, at) ==
    /\ id \in DOMAIN objects
    /\ LET old == objects[id]
           msg == [ address |-> old.promise.tags.target,
                    message |-> [ tag     |-> "Execute",
                                  id      |-> id,
                                  version |-> old.task.version ] ]
       IN  /\ old.task.state = "pending"
           /\ old.task.retryTimeoutAt /= NoTime
           /\ old.task.retryTimeoutAt <= at
           /\ Project(old, at).promise.state = "pending"
           /\ objects' =
                Write(objects, id,
                      [old EXCEPT
                          !.task.retryTimeoutAt = at + RetryDelay])
           /\ network' \in {network, NetworkWrite(network, msg)}

ProcessCallback(awaited, awaiter, at) ==
    /\ awaited \in DOMAIN objects
    /\ awaiter \in objects[awaited].promise.callbacks
    /\ Project(objects[awaited], at).promise.state /= "pending"
    /\ objects' = CallbackObjects(objects, awaited, awaiter, at)
    /\ UNCHANGED network

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

-----------------------------------------------------------------------------
(* Direct request actions. A disabled handler disables the corresponding
   action; [][Next]_vars still admits protocol stuttering. *)

PromiseCreate(req, at) ==
    \E os \in HandlePromiseCreate(objects, req, at) : Store(os)

PromiseSettle(req, at) ==
    \E os \in HandlePromiseSettle(objects, req, at) : Store(os)

PromiseRegisterCallback(req, at) ==
    \E os \in HandlePromiseRegisterCallback(objects, req, at) : Store(os)

PromiseRegisterListener(req, at) ==
    \E os \in HandlePromiseRegisterListener(objects, req, at) : Store(os)

TaskCreate(req, at) ==
    \E os \in HandleTaskCreate(objects, req, at) : Store(os)

TaskAcquire(req, at) ==
    \E os \in HandleTaskAcquire(objects, req, at) : Store(os)

TaskFence(req, at) ==
    \E os \in HandleTaskFence(objects, req, at) : Store(os)

TaskHeartbeat(req, at) ==
    \E os \in HandleTaskHeartbeat(objects, req, at) : Store(os)

TaskSuspend(req, at) ==
    \E os \in HandleTaskSuspend(objects, req, at) : Store(os)

TaskFulfill(req, at) ==
    \E os \in HandleTaskFulfill(objects, req, at) : Store(os)

TaskRelease(req, at) ==
    \E os \in HandleTaskRelease(objects, req, at) : Store(os)

TaskHalt(req, at) ==
    \E os \in HandleTaskHalt(objects, req, at) : Store(os)

TaskContinue(req, at) ==
    \E os \in HandleTaskContinue(objects, req, at) : Store(os)

-----------------------------------------------------------------------------

Init ==
    /\ objects = EmptyFn
    /\ network = {}

AnyPromiseTimeout ==
    \E id \in Id, at \in Horizon : PromiseTimeout(id, at)

AnyLeaseTimeout ==
    \E id \in Id, at \in Horizon : LeaseTimeout(id, at)

AnyRetryTimeout ==
    \E id \in Id, at \in Horizon : RetryTimeout(id, at)

AnyCallback ==
    \E awaited, awaiter \in Id, at \in Horizon :
        ProcessCallback(awaited, awaiter, at)

AnyListener ==
    \E id \in Id, address \in Address : ProcessListener(id, address)

DirectNext ==
    \/ AnyPromiseTimeout
    \/ AnyLeaseTimeout
    \/ AnyRetryTimeout
    \/ AnyCallback
    \/ AnyListener
    \/ \E req \in CreateReq, at \in Horizon : PromiseCreate(req, at)
    \/ \E req \in SettleReq, at \in Horizon : PromiseSettle(req, at)
    \/ \E req \in CallbackReq, at \in Horizon :
          PromiseRegisterCallback(req, at)
    \/ \E req \in [awaited : Id, address : Address], at \in Horizon :
          PromiseRegisterListener(req, at)
    \/ \E req \in [pid : Pid, ttl : Ttl, action : CreateReq],
          at \in Horizon : TaskCreate(req, at)
    \/ \E req \in [id : Id, version : Version, pid : Pid, ttl : Ttl],
          at \in Horizon : TaskAcquire(req, at)
    \/ \E req \in [id : Id, version : Version, action : FenceAction],
          at \in Horizon : TaskFence(req, at)
    \/ \E req \in [pid : Pid, tasks : SUBSET TaskRefT],
          at \in Horizon : TaskHeartbeat(req, at)
    \/ \E req \in [id : Id, version : Version,
                    actions : SUBSET CallbackReq],
          at \in Horizon : TaskSuspend(req, at)
    \/ \E req \in [id : Id, version : Version, action : SettleReq],
          at \in Horizon : TaskFulfill(req, at)
    \/ \E req \in TaskRefT, at \in Horizon : TaskRelease(req, at)
    \/ \E req \in [id : Id], at \in Horizon : TaskHalt(req, at)
    \/ \E req \in [id : Id], at \in Horizon : TaskContinue(req, at)

Next ==
    DirectNext \/ Batch

Fairness ==
    /\ WF_vars(AnyPromiseTimeout)
    /\ WF_vars(AnyLeaseTimeout)
    /\ WF_vars(AnyRetryTimeout)
    /\ WF_vars(AnyCallback)
    /\ WF_vars(AnyListener)

Spec ==
    Init /\ [][Next]_vars /\ Fairness

Safety ==
    Init /\ [][Next]_vars

-----------------------------------------------------------------------------

VersionBound ==
    \A id \in DOMAIN objects :
        objects[id].task.version <= MaxVersion

TypeOK ==
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
