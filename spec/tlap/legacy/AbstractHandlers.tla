-------------------------- MODULE AbstractHandlers --------------------------
(* Pure request handlers shared by the swept and direct abstract machines.
   A handler returns the object maps it can produce, or the empty set when
   disabled. It does not update either machine's message variable. *)
EXTENDS Requests

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

=============================================================================
