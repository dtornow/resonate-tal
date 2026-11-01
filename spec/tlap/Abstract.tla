----------------------------- MODULE Abstract -----------------------------
EXTENDS Requests

VARIABLES
    objects,    \* partial: DOMAIN is what exists
    outbox,     \* at most one entry per MsgKey
    now         \* the clock. NOT part of the store: a server does not own

vars ==
    <<objects, outbox, now>>

-----------------------------------------------------------------------------

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

(* A handler reads the swept store, which is not `objects` yet, and returns
   the object-maps it can produce. None, when it is disabled. It does not
   touch the outbox: a message is a due action's effect. `t` is the time
   the decision was made. It is at most the clock, and the clock stays. *)

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

(* The nested create or settle sees this store. It is not swept again. *)
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

-----------------------------------------------------------------------------

(* Drop a set of listener addresses and keep every other field. The same
   record a one-address step writes. *)
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

(* One due action, as the store it produces. The promise, the lease and the
   callback leave the outbox alone. A retry enqueues Execute; a listener
   enqueues Unblock. *)

DuePromise(o, b, t) ==
    { [ objects |-> Write(o, i, Project(o[i], t)),
        outbox  |-> b ] :
        i \in { j \in DOMAIN o :
                  /\ o[j].promise.state = "pending"
                  /\ o[j].promise.timeoutAt <= t } }

DueLease(o, b, t) ==
    { LET old == o[i]
      IN  [ objects |-> Write(o, i,
                    [old EXCEPT !.task.state          = "pending",
                                !.task.pid            = NoPid,
                                !.task.ttl            = NoTime,
                                !.task.leaseTimeoutAt = NoTime,
                                !.task.retryTimeoutAt = t]),
            outbox  |-> b ] :
        i \in { j \in DOMAIN o :
                  LET old == o[j]
                  IN  /\ old.task.state = "acquired"
                      /\ old.task.leaseTimeoutAt /= NoTime
                      /\ old.task.leaseTimeoutAt <= t
                      /\ Project(old, t).promise.state = "pending" } }

DueRetry(o, b, t) ==
    { LET old == o[i]
          msg == [ address |-> old.promise.tags.target,
                   message |-> [ tag     |-> "Execute",
                                 id      |-> i,
                                 version |-> old.task.version ] ]
      IN  [ objects |-> Write(o, i, [old EXCEPT !.task.retryTimeoutAt = t + RetryTimeout]),
            outbox  |-> { kept \in b : MsgKey(kept) /= MsgKey(msg) } \cup {msg} ] :
        i \in { j \in DOMAIN o :
                  LET old == o[j]
                  IN  /\ old.task.state = "pending"
                      /\ old.task.retryTimeoutAt /= NoTime
                      /\ old.task.retryTimeoutAt <= t
                      /\ Project(old, t).promise.state = "pending" } }

DueListener(o, b, t) ==
    LET ids == { j \in DOMAIN o : Project(o[j], t).promise.state /= "pending" }
    IN  IF ids = {} THEN
            {}
        ELSE
            UNION { { LET awaited == Project(o[i], t)
                           msg     == [ address |-> a,
                                        message |-> [ tag   |-> "Unblock",
                                                      id    |-> i,
                                                      state |-> awaited.promise.state ] ]
                       IN  [ objects |-> Write(o, i, WithoutListeners(awaited, {a})),
                             outbox  |-> { kept \in b : MsgKey(kept) /= MsgKey(msg) } \cup {msg} ] :
                       a \in o[i].promise.listeners } :
                    i \in ids }

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

(* A suspended awaiter starts its resume set over. Any other live task
   keeps the resumes it already had. *)
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

CallbackObjects(o, i, w, t) ==
    LET awaited    == Project(o[i], t)
        newAwaited == WithoutCallbacks(awaited, {w})
        struck     == Write(o, i, newAwaited)
    IN  IF w \notin DOMAIN o THEN
            struck
        ELSE
            LET awaiter == Project(struck[w], t)
            IN  IF awaiter.task.state \in {"none", "fulfilled"} THEN
                    Write(struck, w, awaiter)
                ELSE IF awaiter.task.state = "suspended" THEN
                    Write(struck, w, WakeSuspended(awaiter, {i}, t))
                ELSE
                    Write(struck, w, UnionResumes(awaiter, {i}))

DueCallback(o, b, t) ==
    LET ids == { j \in DOMAIN o : Project(o[j], t).promise.state /= "pending" }
    IN  IF ids = {} THEN
            {}
        ELSE
            UNION { { [ objects |-> CallbackObjects(o, i, w, t),
                        outbox  |-> b ] :
                      w \in o[i].promise.callbacks } :
                    i \in ids }

Due1(o, b, t) ==
    DuePromise(o, b, t) \cup DueLease(o, b, t) \cup DueRetry(o, b, t)
        \cup DueListener(o, b, t) \cup DueCallback(o, b, t)

(* The same action, named, so fairness can ask for one item with the clock
   left where it is. A step of `Next` that does exactly this is one of them. *)
ProcessPromiseTimeout ==
    \E nxt \in DuePromise(objects, outbox, now) :
        /\ objects' = nxt.objects
        /\ outbox'  = nxt.outbox
        /\ UNCHANGED now

ProcessLeaseTimeout ==
    \E nxt \in DueLease(objects, outbox, now) :
        /\ objects' = nxt.objects
        /\ outbox'  = nxt.outbox
        /\ UNCHANGED now

ProcessRetryTimeout ==
    \E nxt \in DueRetry(objects, outbox, now) :
        /\ objects' = nxt.objects
        /\ outbox'  = nxt.outbox
        /\ UNCHANGED now

ProcessListener ==
    \E nxt \in DueListener(objects, outbox, now) :
        /\ objects' = nxt.objects
        /\ outbox'  = nxt.outbox
        /\ UNCHANGED now

ProcessCallback ==
    \E nxt \in DueCallback(objects, outbox, now) :
        /\ objects' = nxt.objects
        /\ outbox'  = nxt.outbox
        /\ UNCHANGED now

-----------------------------------------------------------------------------

(* `Swept` is every store reachable by due actions, including the current
   one. Any enabled order, any length up to the bound: one promise timeout,
   one lease timeout and one retry per object, plus one listener per address
   and one callback per id. *)

MaxSweep ==
    Cardinality(Id) * (Cardinality(Id) + Cardinality(Address) + 3)

Swept(t) ==
    LET R[k \in 0 .. MaxSweep] ==
            IF k = 0 THEN
                {[objects |-> objects, outbox |-> outbox]}
            ELSE
                LET prev == R[k - 1]
                IN  prev \cup Flat({Due1(st.objects, st.outbox, t) : st \in prev})
    IN  R[MaxSweep]

Handled(o, t) ==
       Flat({HandlePromiseCreate(o, req, t) : req \in CreateReq})
    \cup Flat({HandlePromiseSettle(o, req, t) : req \in SettleReq})
    \cup Flat({HandlePromiseRegisterCallback(o, req, t) : req \in CallbackReq})
    \cup Flat({HandlePromiseRegisterListener(o, req, t) : req \in [awaited : Id, address : Address]})
    \cup Flat({HandleTaskCreate(o, req, t) : req \in [pid : Pid, ttl : Ttl, action : CreateReq]})
    \cup Flat({HandleTaskAcquire(o, req, t) : req \in [id : Id, version : Version, pid : Pid, ttl : Ttl]})
    \cup Flat({HandleTaskFence(o, i, v, t) : i \in Id, v \in Version})
    \cup Flat({HandleTaskHeartbeat(o, req, t) : req \in [pid : Pid, tasks : SUBSET TaskRefT]})
    \cup Flat({HandleTaskSuspend(o, req, t) : req \in [id : Id, version : Version, actions : SUBSET CallbackReq]})
    \cup Flat({HandleTaskFulfill(o, req, t) : req \in [id : Id, version : Version, action : SettleReq]})
    \cup Flat({HandleTaskRelease(o, req, t) : req \in TaskRefT})
    \cup Flat({HandleTaskHalt(o, req, t) : req \in [id : Id]})
    \cup Flat({HandleTaskContinue(o, req, t) : req \in [id : Id]})

(* The work is stamped with the decision time. The clock is not part of it. *)
Apply(pre, os) ==
    /\ objects' = os
    /\ outbox'  = pre.outbox
    /\ UNCHANGED now

Clock ==
    /\ now' = now + 1
    /\ UNCHANGED <<objects, outbox>>

-----------------------------------------------------------------------------

Init ==
    /\ objects = EmptyFn
    /\ outbox  = {}
    /\ now     = 0

(* A step picks a decision time at most the clock, sweeps what was due then,
   and may apply a handler. The clock stays. By itself the clock only ticks. *)
Next ==
    \/ \E t \in 0 .. now :
          LET reached == Swept(t)
          IN  \/ \E pre \in reached :
                    \E os \in Handled(pre.objects, t) :
                        Apply(pre, os)
              \/ \E pre \in reached :
                    /\ \/ pre.objects /= objects
                       \/ pre.outbox /= outbox
                    /\ objects' = pre.objects
                    /\ outbox'  = pre.outbox
                    /\ UNCHANGED now
    \/ Clock

Fairness ==
    /\ WF_vars(ProcessPromiseTimeout)
    /\ WF_vars(ProcessLeaseTimeout)
    /\ WF_vars(ProcessRetryTimeout)
    /\ WF_vars(ProcessListener)
    /\ WF_vars(ProcessCallback)
    /\ WF_vars(Clock)

Spec ==
    Init /\ [][Next]_vars /\ Fairness

Safety ==
    Init /\ [][Next]_vars

-----------------------------------------------------------------------------

(* THE MODEL IS FINITE ONLY IF SOMETHING SAYS SO. `Version` is declared as
   0..MaxVersion and then never enforced: acquire and create bump the task
   version with no upper guard, so a task acquired and released and acquired
   again climbs forever and the state space is infinite. TypeOK did not catch
   it -- it never mentioned version -- and no run of this spec has ever
   terminated. This is the bound, as a state constraint rather than a guard,
   because a protocol that stopped bumping at MaxVersion would be a different
   protocol. *)

NowBound ==
    now <= MaxTime

VersionBound ==
    \A i \in DOMAIN objects : objects[i].task.version <= MaxVersion

TypeOK ==
    /\ now \in Time
    /\ DOMAIN objects \subseteq Id
        /\ \A a, b \in outbox : MsgKey(a) = MsgKey(b) => a = b
        /\ \A o \in DOMAIN objects :
           objects[o].task.state = "none" => objects[o].task = NoTask

well_formed_promise_created_at_lte_timeout_at ==
    \A i \in DOMAIN objects : objects[i].promise.createdAt <= objects[i].promise.timeoutAt

well_formed_promise_settled_at_iff_not_pending ==
    \A i \in DOMAIN objects :
        (objects[i].promise.state /= "pending") <=> (objects[i].promise.settledAt /= NoTime)

well_formed_promise_pending_has_no_value ==
    \A i \in DOMAIN objects :
        objects[i].promise.state = "pending" => objects[i].promise.value = NoValue

well_formed_promise_settled_at_lte_timeout_at ==
    \A i \in DOMAIN objects :
        objects[i].promise.settledAt /= NoTime => objects[i].promise.settledAt <= objects[i].promise.timeoutAt

well_formed_task_pending_iff_has_retry_timeout_at ==
    \A i \in DOMAIN objects :
        objects[i].task.state /= "none" => ((objects[i].task.state = "pending") <=> (objects[i].task.retryTimeoutAt /= NoTime))

well_formed_task_acquired_iff_has_lease_timeout_at ==
    \A i \in DOMAIN objects :
        objects[i].task.state /= "none" => ((objects[i].task.state = "acquired") <=> (objects[i].task.leaseTimeoutAt /= NoTime))

consistent_settled_promise_has_fulfilled_task ==
    \A i \in DOMAIN objects :
        (objects[i].promise.state /= "pending" /\ objects[i].task.state /= "none") => objects[i].task.state = "fulfilled"

consistent_settled_task_promise_settled ==
    \A i \in DOMAIN objects :
        (objects[i].task.state /= "none" /\ objects[i].task.state = "fulfilled") => objects[i].promise.state /= "pending"

consistent_task_iff_targeted_promise ==
    \A i \in DOMAIN objects : objects[i].task.state /= "none" <=> objects[i].promise.tags.targeted

preserved_settled_promise_record ==
    \A i \in DOMAIN objects :
        \/ objects[i].promise.state = "pending"
        \/ /\ i \in DOMAIN objects'
           /\ objects'[i].promise.state     = objects[i].promise.state
           /\ objects'[i].promise.settledAt = objects[i].promise.settledAt
           /\ objects'[i].promise.value     = objects[i].promise.value

consistent_new_promise_born_clean ==
    \A i \in DOMAIN objects' :
        \/ i \in DOMAIN objects
        \/ LET q == objects'[i].promise IN
           /\ q.callbacks = {}
           /\ q.listeners = {}
           /\ q.value = NoValue
           /\ q.createdAt <= now
           /\ \/ /\ q.state = "pending"
                 /\ q.settledAt = NoTime
                 /\ q.createdAt < q.timeoutAt
              \/ /\ q.settledAt = q.timeoutAt
                 /\ q.createdAt = q.timeoutAt
                 /\ q.timeoutAt <= now
                 /\ IF q.tags.timer THEN q.state = "resolved"
                                    ELSE q.state = "rejectedTimedout"

consistent_promise_settlement_stamp ==
    \A i \in DOMAIN objects :
        \/ objects[i].promise.state /= "pending"
        \/ /\ i \in DOMAIN objects'
           /\ LET q == objects'[i].promise IN
              \/ q.state = "pending"
              \/ /\ q.settledAt <= now
                 /\ q.settledAt < q.timeoutAt
                 /\ q.state /= "rejectedTimedout"
              \/ /\ q.settledAt = q.timeoutAt
                 /\ q.timeoutAt <= now
                 /\ (IF q.tags.timer THEN q.state = "resolved"
                                     ELSE q.state = "rejectedTimedout")
                 /\ q.value = objects[i].promise.value

consistent_settlement_fulfils_task ==
    \A i \in DOMAIN objects :
        \/ objects[i].promise.state /= "pending"
        \/ i \notin DOMAIN objects'
        \/ objects'[i].promise.state = "pending"
        \/ objects'[i].task.state \in {"none", "fulfilled"}

-----------------------------------------------------------------------------

UnitCoherent ==
    \A o \in DOMAIN objects :
        (/\ objects[o].promise.state /= "pending"
         /\ objects[o].task.state \notin {"none", "fulfilled"})
            => FALSE

-----------------------------------------------------------------------------

SameOrigin ==
    \A o \in DOMAIN objects :
        \A w \in objects[o].promise.callbacks : w.origin = o.origin

T_preserved_settled_promise_record ==
    [][preserved_settled_promise_record]_vars

T_consistent_new_promise_born_clean ==
    [][consistent_new_promise_born_clean]_vars

T_consistent_promise_settlement_stamp ==
    [][consistent_promise_settlement_stamp]_vars

T_consistent_settlement_fulfils_task ==
    [][consistent_settlement_fulfils_task]_vars

================================================================

=============================================================================
