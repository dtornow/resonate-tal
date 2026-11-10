-------------------------- MODULE AbstractBatch --------------------------
(***************************************************************************)
(* A declarative batching adapter for Abstract. Abstract!Next remains the   *)
(* direct, one-action protocol. Batch is an additional atomic relation for  *)
(* executors that replace one whole document with a CAS.                    *)
(*                                                                         *)
(* A witness has six fixed stages. Each internal stage chooses any subset   *)
(* of the actions eligible at that stage, including the empty subset; the   *)
(* request stage chooses zero or one enabled request. Batch requires at      *)
(* least one chosen action. There is no recursive reachability relation and *)
(* no sweep bound.                                                          *)
(***************************************************************************)
EXTENDS Abstract

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

(* Direct Abstract actions are intentionally still present. *)
BatchNext ==
    Next \/ Batch

BatchSpec ==
    Init /\ [][BatchNext]_vars /\ Fairness

BatchSafety ==
    Init /\ [][BatchNext]_vars

=============================================================================
