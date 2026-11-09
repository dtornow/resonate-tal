----------------------------- MODULE Abstract -----------------------------
EXTENDS AbstractHandlers

VARIABLES
    objects,    \* partial: DOMAIN is what exists
    outbox,     \* at most one entry per MsgKey
    now         \* the clock. NOT part of the store: a server does not own

vars ==
    <<objects, outbox, now>>

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
      IN  [ objects |-> Write(o, i, [old EXCEPT !.task.retryTimeoutAt = t + RetryDelay]),
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
