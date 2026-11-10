-------------------------------- MODULE Concrete --------------------------------

EXTENDS Requests

VARIABLES
    docs,
    timeouts,
    outbox,
    steps,
    now

vars ==
    <<docs, timeouts, outbox, steps, now>>

-----------------------------------------------------------------------------

New(req, t) ==
    IF req.timeoutAt > t THEN
        [ promise |-> [ state |-> "pending", param |-> req.param, value |-> NoValue,
                        tags |-> req.tags, timeoutAt |-> req.timeoutAt,
                        createdAt |-> t, settledAt |-> NoTime,
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

Skip(doc) ==
    [ doc   |-> doc,
      puts  |-> << >>,
      dels  |-> << >>,
      sends |-> << >> ]

HandlePromiseCreate(req, doc, t) ==
    IF req.id \in DOMAIN doc THEN
        Skip(doc)
    ELSE
        LET new == New(req, t)
        IN
            [ doc   |-> Write(doc, req.id, new),
              puts  |-> (IF new.promise.state = "pending" THEN
                             << [at |-> req.timeoutAt, id |-> req.id, kind |-> "promise"] >>
                         ELSE << >>)
                     \o (IF new.task.state = "pending" THEN
                             << [at |-> t, id |-> req.id, kind |-> "retry"] >>
                         ELSE << >>),
              dels  |-> << >>,
              sends |-> << >> ]

HandlePromiseSettle(req, doc, t) ==
    IF req.id \notin DOMAIN doc THEN
        Skip(doc)
    ELSE
        LET old == Project(doc[req.id], t)
            new == [ promise |-> [old.promise EXCEPT !.state     = req.state,
                                                     !.value     = req.value,
                                                     !.settledAt = t],
                     task    |-> [old.task EXCEPT !.state          = IF @ = "none" THEN "none"
                                                                     ELSE "fulfilled",
                                                  !.pid            = NoPid,
                                                  !.ttl            = NoTime,
                                                  !.leaseTimeoutAt = NoTime,
                                                  !.retryTimeoutAt = NoTime,
                                                  !.resumes        = {}] ]
        IN
            IF old.promise.state /= "pending" THEN
                Skip(doc)
            ELSE
                [ doc   |-> Write(doc, req.id, new),
                  puts  |-> << >>,
                  dels  |-> << [at |-> old.promise.timeoutAt, id |-> req.id, kind |-> "promise"] >>
                         \o (IF old.task.state = "acquired" THEN
                                 << [at |-> old.task.leaseTimeoutAt, id |-> req.id, kind |-> "lease"] >>
                             ELSE << >>)
                         \o (IF old.task.state = "pending" THEN
                                 << [at |-> old.task.retryTimeoutAt, id |-> req.id, kind |-> "retry"] >>
                             ELSE << >>),
                  sends |-> << >> ]

HandlePromiseRegisterCallback(req, doc, t) ==
    IF \/ req.awaited \notin DOMAIN doc
       \/ req.awaiter \notin DOMAIN doc THEN
        Skip(doc)
    ELSE
        LET awaited    == Project(doc[req.awaited], t)
            awaiter    == Project(doc[req.awaiter], t)
            newAwaited == [awaited EXCEPT !.promise.callbacks = @ \cup {req.awaiter}]
        IN
            IF \/ ~awaiter.promise.tags.targeted
               \/ ~IsExternal(awaited.promise)
               \/ awaited.promise.state /= "pending"
               \/ awaiter.promise.state /= "pending" THEN
                Skip(doc)
            ELSE
                [ doc   |-> Write(doc, req.awaited, newAwaited),
                  puts  |-> << >>,
                  dels  |-> << >>,
                  sends |-> << >> ]

HandlePromiseRegisterListener(req, doc, t) ==
    IF req.awaited \notin DOMAIN doc THEN
        Skip(doc)
    ELSE
        LET old == Project(doc[req.awaited], t)
            new == [old EXCEPT !.promise.listeners = @ \cup {req.address}]
        IN
            IF \/ ~IsExternal(old.promise)
               \/ old.promise.state /= "pending" THEN
                Skip(doc)
            ELSE
                [ doc   |-> Write(doc, req.awaited, new),
                  puts  |-> << >>,
                  dels  |-> << >>,
                  sends |-> << >> ]

HandleTaskCreate(req, doc, t) ==
    IF ~req.action.tags.targeted THEN
        Skip(doc)
    ELSE IF req.action.id \notin DOMAIN doc THEN
        LET born == New(req.action, t)
            new  == IF born.promise.state = "pending" THEN
                        [born EXCEPT !.task.state          = "acquired",
                                     !.task.version        = @ + 1,
                                     !.task.ttl            = req.ttl,
                                     !.task.pid            = req.pid,
                                     !.task.leaseTimeoutAt = t + req.ttl,
                                     !.task.retryTimeoutAt = NoTime,
                                     !.task.resumes        = {}]
                    ELSE
                        born
        IN
            [ doc   |-> Write(doc, req.action.id, new),
              puts  |-> IF born.promise.state = "pending" THEN
                            << [at |-> req.action.timeoutAt, id |-> req.action.id, kind |-> "promise"],
                               [at |-> t + req.ttl,          id |-> req.action.id, kind |-> "lease"] >>
                        ELSE << >>,
              dels  |-> << >>,
              sends |-> << >> ]
    ELSE
        LET old == Project(doc[req.action.id], t)
            new == [old EXCEPT !.task.state          = "acquired",
                               !.task.version        = @ + 1,
                               !.task.ttl            = req.ttl,
                               !.task.pid            = req.pid,
                               !.task.leaseTimeoutAt = t + req.ttl,
                               !.task.retryTimeoutAt = NoTime,
                               !.task.resumes        = {}]
        IN
            IF \/ ~old.promise.tags.targeted
               \/ old.task.state /= "pending" THEN
                Skip(doc)
            ELSE
                [ doc   |-> Write(doc, req.action.id, new),
                  puts  |-> << [at |-> t + req.ttl, id |-> req.action.id, kind |-> "lease"] >>,
                  dels  |-> << [at |-> old.task.retryTimeoutAt, id |-> req.action.id, kind |-> "retry"] >>,
                  sends |-> << >> ]

HandleTaskAcquire(req, doc, t) ==
    IF req.id \notin DOMAIN doc THEN
        Skip(doc)
    ELSE
        LET old == Project(doc[req.id], t)
            new == [old EXCEPT !.task.state          = "acquired",
                               !.task.version        = @ + 1,
                               !.task.ttl            = req.ttl,
                               !.task.pid            = req.pid,
                               !.task.leaseTimeoutAt = t + req.ttl,
                               !.task.retryTimeoutAt = NoTime,
                               !.task.resumes        = {}]
        IN
            IF \/ old.task.state /= "pending"
               \/ old.promise.state /= "pending"
               \/ old.task.version /= req.version THEN
                Skip(doc)
            ELSE
                [ doc   |-> Write(doc, req.id, new),
                  puts  |-> << [at |-> t + req.ttl, id |-> req.id, kind |-> "lease"] >>,
                  dels  |-> << [at |-> old.task.retryTimeoutAt, id |-> req.id, kind |-> "retry"] >>,
                  sends |-> << >> ]

HandleTaskFence(req, doc, t) ==
    IF req.id \notin DOMAIN doc THEN
        Skip(doc)
    ELSE
        LET old == Project(doc[req.id], t)
        IN
            IF \/ req.action.req.id = req.id
               \/ req.action.req.id.origin /= req.id.origin
               \/ old.task.state /= "acquired"
               \/ old.promise.state /= "pending"
               \/ old.task.version /= req.version THEN
                Skip(doc)
            ELSE IF req.action.tag = "Create" THEN
                HandlePromiseCreate(req.action.req, doc, t)
            ELSE
                HandlePromiseSettle(req.action.req, doc, t)

HandleTaskHeartbeat(req, doc, t) ==
    LET beat == { i \in DOMAIN doc :
                    LET old == Project(doc[i], t)
                    IN  /\ \E rf \in req.tasks :
                              rf.id = i /\ rf.version = old.task.version
                        /\ old.task.state = "acquired"
                        /\ old.task.pid = req.pid
                        /\ old.promise.state = "pending" }
        q    == SetToSeq({ i \in beat :
                             t + doc[i].task.ttl /= doc[i].task.leaseTimeoutAt })
    IN
        IF beat = {} THEN
            Skip(doc)
        ELSE
        [ doc   |-> [ i \in DOMAIN doc |->
                         IF i \in beat THEN
                             LET old == Project(doc[i], t)
                             IN  [old EXCEPT !.task.leaseTimeoutAt =
                                                 t + old.task.ttl]
                         ELSE
                             doc[i] ],
          puts  |-> [ n \in 1 .. Len(q) |->
                        [at |-> t + doc[q[n]].task.ttl, id |-> q[n], kind |-> "lease"] ],
          dels  |-> [ n \in 1 .. Len(q) |->
                        [at |-> doc[q[n]].task.leaseTimeoutAt, id |-> q[n], kind |-> "lease"] ],
          sends |-> << >> ]

HandleTaskSuspend(req, doc, t) ==
    LET aw   == { a.awaited : a \in req.actions }
        seen == { a \in aw : a \in DOMAIN doc }
    IN
        IF \/ req.actions = {}
           \/ req.id \in aw
           \/ \E a \in aw : a.origin /= req.id.origin
           \/ req.id \notin DOMAIN doc
           \/ seen /= aw THEN
            Skip(doc)
        ELSE
            LET old == Project(doc[req.id], t)
                new == [old EXCEPT !.task.state          = "suspended",
                                   !.task.pid            = NoPid,
                                   !.task.ttl            = NoTime,
                                   !.task.leaseTimeoutAt = NoTime,
                                   !.task.retryTimeoutAt = NoTime,
                                   !.task.resumes        = {}]
            IN
                IF \/ old.task.state /= "acquired"
                   \/ old.promise.state /= "pending"
                   \/ old.task.version /= req.version
                   \/ \E a \in aw :
                        ~IsExternal(Project(doc[a], t).promise) THEN
                    Skip(doc)
                ELSE IF \E a \in aw :
                          Project(doc[a], t).promise.state /= "pending" THEN
                    [ doc   |-> Write(doc, req.id, [old EXCEPT !.task.resumes = {}]),
                      puts  |-> << >>,
                      dels  |-> << >>,
                      sends |-> << >> ]
                ELSE
                    [ doc   |-> [ i \in DOMAIN doc |->
                                     IF i = req.id THEN
                                         new
                                     ELSE IF i \in aw THEN
                                         [Project(doc[i], t) EXCEPT
                                              !.promise.callbacks = @ \cup {req.id}]
                                     ELSE
                                         doc[i] ],
                      puts  |-> << >>,
                      dels  |-> << [at |-> old.task.leaseTimeoutAt, id |-> req.id, kind |-> "lease"] >>,
                      sends |-> << >> ]

HandleTaskFulfill(req, doc, t) ==
    IF req.id \notin DOMAIN doc THEN
        Skip(doc)
    ELSE
        LET old == Project(doc[req.id], t)
            new == [ promise |-> [old.promise EXCEPT !.state     = req.action.state,
                                                     !.value     = req.action.value,
                                                     !.settledAt = t],
                     task    |-> [old.task EXCEPT !.state          = "fulfilled",
                                                  !.pid            = NoPid,
                                                  !.ttl            = NoTime,
                                                  !.leaseTimeoutAt = NoTime,
                                                  !.retryTimeoutAt = NoTime,
                                                  !.resumes        = {}] ]
        IN
            IF \/ old.task.state /= "acquired"
               \/ old.promise.state /= "pending"
               \/ old.task.version /= req.version THEN
                Skip(doc)
            ELSE
                [ doc   |-> Write(doc, req.id, new),
                  puts  |-> << >>,
                  dels  |-> << [at |-> old.promise.timeoutAt, id |-> req.id, kind |-> "promise"],
                               [at |-> old.task.leaseTimeoutAt,    id |-> req.id, kind |-> "lease"] >>,
                  sends |-> << >> ]

HandleTaskRelease(req, doc, t) ==
    IF req.id \notin DOMAIN doc THEN
        Skip(doc)
    ELSE
        LET old == Project(doc[req.id], t)
            new == [old EXCEPT !.task.state          = "pending",
                               !.task.pid            = NoPid,
                               !.task.ttl            = NoTime,
                               !.task.leaseTimeoutAt = NoTime,
                               !.task.retryTimeoutAt = t]
        IN
            IF \/ old.task.state /= "acquired"
               \/ old.promise.state /= "pending"
               \/ old.task.version /= req.version THEN
                Skip(doc)
            ELSE
                [ doc   |-> Write(doc, req.id, new),
                  puts  |-> << [at |-> t, id |-> req.id, kind |-> "retry"] >>,
                  dels  |-> << [at |-> old.task.leaseTimeoutAt, id |-> req.id, kind |-> "lease"] >>,
                  sends |-> << >> ]

HandleTaskHalt(req, doc, t) ==
    IF req.id \notin DOMAIN doc THEN
        Skip(doc)
    ELSE
        LET old == Project(doc[req.id], t)
            new == [old EXCEPT !.task.state          = "halted",
                               !.task.pid            = NoPid,
                               !.task.ttl            = NoTime,
                               !.task.leaseTimeoutAt = NoTime,
                               !.task.retryTimeoutAt = NoTime]
        IN
            IF \/ old.task.state = "none"
               \/ old.task.state \in {"fulfilled", "halted"} THEN
                Skip(doc)
            ELSE
                [ doc   |-> Write(doc, req.id, new),
                  puts  |-> << >>,
                  dels  |-> (IF old.task.state = "acquired" THEN
                                 << [at |-> old.task.leaseTimeoutAt, id |-> req.id, kind |-> "lease"] >>
                             ELSE << >>)
                         \o (IF old.task.state = "pending" THEN
                                 << [at |-> old.task.retryTimeoutAt, id |-> req.id, kind |-> "retry"] >>
                             ELSE << >>),
                  sends |-> << >> ]

HandleTaskContinue(req, doc, t) ==
    IF req.id \notin DOMAIN doc THEN
        Skip(doc)
    ELSE
        LET old == Project(doc[req.id], t)
            new == [old EXCEPT !.task.state          = "pending",
                               !.task.pid            = NoPid,
                               !.task.ttl            = NoTime,
                               !.task.leaseTimeoutAt = NoTime,
                               !.task.retryTimeoutAt = t]
        IN
            IF \/ old.task.state /= "halted"
               \/ old.promise.state /= "pending" THEN
                Skip(doc)
            ELSE
                [ doc   |-> Write(doc, req.id, new),
                  puts  |-> << [at |-> t, id |-> req.id, kind |-> "retry"] >>,
                  dels  |-> << >>,
                  sends |-> << >> ]

Handle(ev, doc, t) ==
    CASE ev.tag = "PromiseCreate" ->
             HandlePromiseCreate(ev.req, doc, t)
      [] ev.tag = "PromiseSettle" ->
             HandlePromiseSettle(ev.req, doc, t)
      [] ev.tag = "PromiseRegisterCallback" ->
             HandlePromiseRegisterCallback(ev.req, doc, t)
      [] ev.tag = "PromiseRegisterListener" ->
             HandlePromiseRegisterListener(ev, doc, t)
      [] ev.tag = "TaskCreate" ->
             HandleTaskCreate(ev, doc, t)
      [] ev.tag = "TaskAcquire" ->
             HandleTaskAcquire(ev, doc, t)
      [] ev.tag = "TaskFence" ->
             HandleTaskFence(ev, doc, t)
      [] ev.tag = "TaskHeartbeat" ->
             HandleTaskHeartbeat(ev, doc, t)
      [] ev.tag = "TaskSuspend" ->
             HandleTaskSuspend(ev, doc, t)
      [] ev.tag = "TaskFulfill" ->
             HandleTaskFulfill(ev, doc, t)
      [] ev.tag = "TaskRelease" ->
             HandleTaskRelease(ev, doc, t)
      [] ev.tag = "TaskHalt" ->
             HandleTaskHalt(ev, doc, t)
      [] ev.tag = "TaskContinue" ->
             HandleTaskContinue(ev, doc, t)
      [] ev.tag = "Timeout" ->
             Skip(doc)

-----------------------------------------------------------------------------

OriginOf(ev) ==
    CASE ev.tag = "PromiseCreate" ->
             ev.req.id.origin
      [] ev.tag = "PromiseSettle" ->
             ev.req.id.origin
      [] ev.tag = "PromiseRegisterCallback" ->
             ev.req.awaited.origin
      [] ev.tag = "PromiseRegisterListener" ->
             ev.awaited.origin
      [] ev.tag = "TaskCreate" ->
             ev.action.id.origin
      [] ev.tag = "TaskAcquire" ->
             ev.id.origin
      [] ev.tag = "TaskFence" ->
             ev.id.origin
      [] ev.tag = "TaskHeartbeat" ->
             CHOOSE o \in Origin : TRUE
      [] ev.tag = "TaskSuspend" ->
             ev.id.origin
      [] ev.tag = "TaskFulfill" ->
             ev.id.origin
      [] ev.tag = "TaskRelease" ->
             ev.id.origin
      [] ev.tag = "TaskHalt" ->
             ev.id.origin
      [] ev.tag = "TaskContinue" ->
             ev.id.origin
      [] ev.tag = "Timeout" ->
             ev.origin

-----------------------------------------------------------------------------

Merge(a, b) ==
    [ doc   |-> b.doc,
      puts  |-> a.puts  \o b.puts,
      dels  |-> a.dels  \o b.dels,
      sends |-> a.sends \o b.sends ]

(* One empty physical timer document wakes an origin at its nearest active
   deadline. The wake performs a full document sweep and schedules the next. *)
ActiveDeadlines(doc) ==
    LET armed ==
            { x \in [id : DOMAIN doc, kind : DeadlineKind] :
                Deadline(doc[x.id], x.kind) /= NoTime }
    IN  { Deadline(doc[x.id], x.kind) : x \in armed }

NextDeadline(doc) ==
    CHOOSE t \in ActiveDeadlines(doc) :
        \A u \in ActiveDeadlines(doc) : t <= u

TimerNames(doc, origin) ==
    IF ActiveDeadlines(doc) = {}
    THEN {}
    ELSE { <<NextDeadline(doc), origin>> }

SweepTimeoutAt(doc, t) ==
    LET S  == { i \in DOMAIN doc :
                  doc[i].promise.state = "pending" /\ doc[i].promise.timeoutAt <= t }
        qp == SetToSeq(S)
        ql == SetToSeq({ i \in S : doc[i].task.state = "acquired" })
        qr == SetToSeq({ i \in S : doc[i].task.state = "pending" })
    IN
    IF S = {} THEN
        [ doc |-> doc, puts |-> << >>, dels |-> << >>, sends |-> << >> ]
    ELSE
    [ doc   |-> [ i \in DOMAIN doc |->
                    IF i \in S THEN Project(doc[i], t) ELSE doc[i] ],
      puts  |-> << >>,
      dels  |->    [ n \in 1 .. Len(qp) |->
                       [at |-> doc[qp[n]].promise.timeoutAt, id |-> qp[n], kind |-> "promise"] ]
                \o [ n \in 1 .. Len(ql) |->
                       [at |-> doc[ql[n]].task.leaseTimeoutAt,    id |-> ql[n], kind |-> "lease"] ]
                \o [ n \in 1 .. Len(qr) |->
                       [at |-> doc[qr[n]].task.retryTimeoutAt,      id |-> qr[n], kind |-> "retry"] ],
      sends |-> << >> ]

(* The same record a listener step writes: every field kept, the
   addresses gone. *)
DropListeners(obj) ==
    [ promise |-> [ state     |-> obj.promise.state,
                    param     |-> obj.promise.param,
                    value     |-> obj.promise.value,
                    tags      |-> obj.promise.tags,
                    timeoutAt |-> obj.promise.timeoutAt,
                    createdAt |-> obj.promise.createdAt,
                    settledAt |-> obj.promise.settledAt,
                    callbacks |-> obj.promise.callbacks,
                    listeners |-> {} ],
      task    |-> obj.task ]

DropCallbacks(obj) ==
    [ promise |-> [ state     |-> obj.promise.state,
                    param     |-> obj.promise.param,
                    value     |-> obj.promise.value,
                    tags      |-> obj.promise.tags,
                    timeoutAt |-> obj.promise.timeoutAt,
                    createdAt |-> obj.promise.createdAt,
                    settledAt |-> obj.promise.settledAt,
                    callbacks |-> {},
                    listeners |-> obj.promise.listeners ],
      task    |-> obj.task ]

Wake(obj, src, t) ==
    [ promise |-> obj.promise,
      task    |-> [ state          |-> "pending",
                    version        |-> obj.task.version,
                    ttl            |-> NoTime,
                    pid            |-> NoPid,
                    leaseTimeoutAt |-> NoTime,
                    retryTimeoutAt |-> t,
                    resumes        |-> src ] ]

AddResumes(obj, R) ==
    [ promise |-> obj.promise,
      task    |-> [ state          |-> obj.task.state,
                    version        |-> obj.task.version,
                    ttl            |-> obj.task.ttl,
                    pid            |-> obj.task.pid,
                    leaseTimeoutAt |-> obj.task.leaseTimeoutAt,
                    retryTimeoutAt |-> obj.task.retryTimeoutAt,
                    resumes        |-> obj.task.resumes \cup R ] ]

SweepListeners(doc, t) ==
    LET pairs == { x \in [id : { i \in DOMAIN doc : doc[i].promise.state /= "pending" },
                          address : Address] :
                      x.address \in doc[x.id].promise.listeners }
        q == SetToSeq(pairs)
    IN
    IF pairs = {} THEN
        [ doc |-> doc, puts |-> << >>, dels |-> << >>, sends |-> << >> ]
    ELSE
    [ doc   |-> [ i \in DOMAIN doc |->
                    IF doc[i].promise.state /= "pending"
                       /\ doc[i].promise.listeners /= {} THEN
                        DropListeners(doc[i])
                    ELSE
                        doc[i] ],
      puts  |-> << >>,
      dels  |-> << >>,
      sends |-> [ n \in 1 .. Len(q) |->
                    [ address |-> q[n].address,
                      message |-> [ tag   |-> "Unblock",
                                    id    |-> q[n].id,
                                    state |-> doc[q[n].id].promise.state ] ] ] ]

SweepCallbacks(doc, t) ==
    LET S == { x \in [id : { i \in DOMAIN doc : doc[i].promise.state /= "pending" },
                    awaiter : Id] :
                   x.awaiter \in doc[x.id].promise.callbacks }
        Resumes(w) == { x.id : x \in { y \in S : y.awaiter = w } }
        Woken      == { x.awaiter : x \in S } \cap DOMAIN doc
        q  == SetToSeq({ w \in Woken : doc[w].task.state = "suspended" })
    IN
    IF S = {} THEN
        [ doc |-> doc, puts |-> << >>, dels |-> << >>, sends |-> << >> ]
    ELSE
    [ doc   |-> [ i \in DOMAIN doc |->
                    LET struck == IF doc[i].promise.state /= "pending"
                                     /\ doc[i].promise.callbacks /= {} THEN
                                      DropCallbacks(doc[i])
                                  ELSE
                                      doc[i]
                    IN
                        IF i \notin Woken \/ struck.task.state \in {"none", "fulfilled"} THEN
                            struck
                        ELSE IF struck.task.state = "suspended" THEN
                            Wake(struck, Resumes(i), t)
                        ELSE
                            AddResumes(struck, Resumes(i)) ],
      puts  |-> [ n \in 1 .. Len(q) |-> [at |-> t, id |-> q[n], kind |-> "retry"] ],
      dels  |-> << >>,
      sends |-> << >> ]

SweepExpiresAt(doc, t) ==
    LET S == { i \in DOMAIN doc :
                 doc[i].task.state = "acquired" /\ doc[i].task.leaseTimeoutAt <= t }
        q == SetToSeq(S)
    IN
    IF S = {} THEN
        [ doc |-> doc, puts |-> << >>, dels |-> << >>, sends |-> << >> ]
    ELSE
    [ doc   |-> [ i \in DOMAIN doc |->
                    IF i \in S THEN
                        [ doc[i] EXCEPT !.task.state          = "pending",
                                        !.task.pid            = NoPid,
                                        !.task.ttl            = NoTime,
                                        !.task.leaseTimeoutAt = NoTime,
                                        !.task.retryTimeoutAt = t ]
                    ELSE
                        doc[i] ],
      puts  |-> [ n \in 1 .. Len(q) |-> [at |-> t, id |-> q[n], kind |-> "retry"] ],
      dels  |-> [ n \in 1 .. Len(q) |->
                    [at |-> doc[q[n]].task.leaseTimeoutAt, id |-> q[n], kind |-> "lease"] ],
      sends |-> << >> ]

SweepRetryAt(doc, t) ==
    LET S == { i \in DOMAIN doc :
                 doc[i].task.state = "pending" /\ doc[i].task.retryTimeoutAt <= t }
        q == SetToSeq(S)
    IN
    IF S = {} THEN
        [ doc |-> doc, puts |-> << >>, dels |-> << >>, sends |-> << >> ]
    ELSE
    [ doc   |-> [ i \in DOMAIN doc |->
                    IF i \in S THEN
                        [ doc[i] EXCEPT !.task.retryTimeoutAt = t + RetryDelay ]
                    ELSE
                        doc[i] ],
      puts  |-> [ n \in 1 .. Len(q) |->
                    [at |-> t + RetryDelay, id |-> q[n], kind |-> "retry"] ],
      dels  |-> [ n \in 1 .. Len(q) |->
                    [at |-> doc[q[n]].task.retryTimeoutAt, id |-> q[n], kind |-> "retry"] ],
      sends |-> [ n \in 1 .. Len(q) |->
                    [ address |-> doc[q[n]].promise.tags.target,
                      message |-> [ tag     |-> "Execute",
                                    id      |-> q[n],
                                    version |-> doc[q[n]].task.version ] ] ] ]

Sweep(doc, t) ==
    LET s1 == SweepTimeoutAt(doc, t)
        s2 == Merge(s1, SweepListeners(s1.doc, t))
        s3 == Merge(s2, SweepCallbacks(s2.doc, t))
        s4 == Merge(s3, SweepExpiresAt(s3.doc, t))
    IN
        Merge(s4, SweepRetryAt(s4.doc, t))

-----------------------------------------------------------------------------

Fresh(ev) ==
    [ ev |-> ev, phase |-> "process", pending |-> << >>,
      expect |-> EmptyFn, at |-> NoTime ]

Set(f, k, v) ==
    [x \in (DOMAIN f) \cup {k} |-> IF x = k THEN v ELSE f[x]]

Del(f, k) ==
    [x \in (DOMAIN f) \ {k} |-> f[x]]

(* Messages committed by a write. The network send is not in this model. *)
Deliver(ob, ms) ==
    LET upto[n \in 0 .. Len(ms)] ==
          IF n = 0 THEN
              ob
          ELSE
              LET acc == upto[n - 1]
              IN  { x \in acc : MsgKey(x) /= MsgKey(ms[n]) } \cup {ms[n]}
    IN
        upto[Len(ms)]

SubmitExternal(ev) ==
    /\ ev \in ExternalEvent
    /\ \E r \in Rid \ DOMAIN steps : steps' = Set(steps, r, Fresh(ev))
    /\ UNCHANGED <<docs, timeouts, outbox, now>>

SubmitInternal(name) ==
    /\ name \in DOMAIN timeouts
    /\ name[1] <= now
    /\ \E r \in Rid \ DOMAIN steps :
           steps' = Set(steps, r,
                        Fresh([tag |-> "Timeout", origin |-> name[2]]))
    /\ UNCHANGED <<docs, timeouts, outbox, now>>

Process(r) ==
    /\ r \in DOMAIN steps
    /\ steps[r].phase = "process"
    \* Timer effects inside handlers are logical deadline metadata. Physical
    \* empty timer documents are reconciled from the workflow before/after.
    /\ LET o     == OriginOf(steps[r].ev)
           swept == Sweep(docs[o], now)
           out   == Handle(steps[r].ev, swept.doc, now)
           final == out.doc
           before == TimerNames(docs[o], o)
           after  == TimerNames(final, o)
           puts  == SetToSeq(after \ before)
           dels  == SetToSeq(before \ after)
           sends == swept.sends \o out.sends
       IN  steps' = [steps EXCEPT ![r].phase   = "perform",
                                  ![r].at      = now,
                                  ![r].pending =
                                      [ n \in 1 .. Len(puts) |->
                                          [tag |-> "PutTimeout", entry |-> puts[n]] ]
                                        \o << [tag |-> "PutDocument", body |-> final,
                                               sends |-> sends] >>
                                        \o [ n \in 1 .. Len(dels) |->
                                               [tag |-> "DelTimeout", entry |-> dels[n]] ],
                                  ![r].expect  = docs[o]]
    /\ UNCHANGED <<docs, timeouts, outbox, now>>

(* Each arm is its own action. A proof can name the one that happened.
   Together they are the old `Perform`. *)
PerformDone(r) ==
    /\ r \in DOMAIN steps
    /\ steps[r].phase = "perform"
    /\ steps[r].pending = << >>
    /\ steps' = Del(steps, r)
    /\ UNCHANGED <<docs, timeouts, outbox, now>>

PerformPutTimeout(r) ==
    /\ r \in DOMAIN steps
    /\ steps[r].phase = "perform"
    /\ steps[r].pending /= << >>
    /\ LET e    == Head(steps[r].pending)
           rest == [steps EXCEPT ![r].pending = Tail(@)]
       IN  /\ e.tag = "PutTimeout"
           /\ timeouts' = Set(timeouts, e.entry, EmptyFn)
           /\ steps'    = rest
           /\ UNCHANGED <<docs, outbox, now>>

PerformPut(r) ==
    /\ r \in DOMAIN steps
    /\ steps[r].phase = "perform"
    /\ steps[r].pending /= << >>
    /\ LET e    == Head(steps[r].pending)
           rest == [steps EXCEPT ![r].pending = Tail(@)]
       IN  /\ e.tag = "PutDocument"
           /\ docs[OriginOf(steps[r].ev)] = steps[r].expect
           /\ docs'   = [docs EXCEPT ![OriginOf(steps[r].ev)] = e.body]
           /\ outbox' = Deliver(outbox, e.sends)
           /\ steps'  = rest
           /\ UNCHANGED <<timeouts, now>>

PerformMiss(r) ==
    /\ r \in DOMAIN steps
    /\ steps[r].phase = "perform"
    /\ steps[r].pending /= << >>
    /\ LET e == Head(steps[r].pending)
       IN  /\ e.tag = "PutDocument"
           /\ docs[OriginOf(steps[r].ev)] /= steps[r].expect
           /\ steps' = [steps EXCEPT ![r].phase   = "process",
                                     ![r].pending = << >>]
           /\ UNCHANGED <<docs, timeouts, outbox, now>>

PerformDelTimeout(r) ==
    /\ r \in DOMAIN steps
    /\ steps[r].phase = "perform"
    /\ steps[r].pending /= << >>
    /\ LET e    == Head(steps[r].pending)
           rest == [steps EXCEPT ![r].pending = Tail(@)]
       IN  /\ e.tag = "DelTimeout"
           /\ timeouts' = Del(timeouts, e.entry)
           /\ steps'    = rest
           /\ UNCHANGED <<docs, outbox, now>>

Perform(r) ==
    \/ PerformDone(r)
    \/ PerformPutTimeout(r)
    \/ PerformPut(r)
    \/ PerformMiss(r)
    \/ PerformDelTimeout(r)

Crash(r) ==
    /\ r \in DOMAIN steps
    /\ steps' = Del(steps, r)
    /\ UNCHANGED <<docs, timeouts, outbox, now>>

Clock ==
    /\ now' = now + 1
    /\ UNCHANGED <<docs, timeouts, outbox, steps>>

Init ==
    /\ docs     = [o \in Origin |-> EmptyFn]
    /\ timeouts = EmptyFn
    /\ outbox   = {}
    /\ steps    = EmptyFn
    /\ now      = 0

Next ==
    \/ \E ev \in ExternalEvent : SubmitExternal(ev)
    \/ \E name \in DOMAIN timeouts : SubmitInternal(name)
    \/ \E r \in DOMAIN steps : Process(r) \/ Perform(r) \/ Crash(r)
    \/ Clock

EventuallyStable ==
    <>[][ \A r \in Rid : ~Crash(r) ]_vars

Fairness ==
    /\ \A r  \in Rid             : WF_vars(Process(r) \/ Perform(r))
    /\ \A o \in Origin :
           SF_vars(\E name \in DOMAIN timeouts :
                       name[2] = o /\ SubmitInternal(name))
    /\ WF_vars(Clock)
    /\ EventuallyStable

FairnessSF ==
    /\ Fairness
    /\ \A r \in Rid : SF_vars(Process(r))
    /\ \A r \in Rid : SF_vars(Perform(r))

Spec ==
    Init /\ [][Next]_vars /\ Fairness

SpecSF ==
    Init /\ [][Next]_vars /\ FairnessSF

-----------------------------------------------------------------------------

C_NowBound ==
    now <= MaxTime

C_VersionBound ==
    \A i \in UNION { DOMAIN docs[o] : o \in Origin } : docs[i.origin][i].task.version <= MaxVersion

TimerNameOK(name) ==
    /\ name = <<name[1], name[2]>>
    /\ name[1] \in Time
    /\ name[2] \in Origin

DeadlineOk ==
    \A name \in DOMAIN timeouts :
        /\ TimerNameOK(name)
        /\ timeouts[name] = EmptyFn

Blob ==
    [ wf |-> docs,
      tm |-> timeouts ]

DocumentTypeOK(doc, origin) ==
    /\ doc = [id \in DOMAIN doc |-> doc[id]]
    /\ DOMAIN doc \subseteq Id
    /\ \A id \in DOMAIN doc :
          /\ id.origin = origin
          /\ doc[id] \in Object

BlobShapeOK ==
    /\ DOMAIN Blob = {"wf", "tm"}
    /\ DOMAIN Blob.wf = Origin

WorkflowStorageTypeOK ==
    /\ BlobShapeOK
    /\ \A origin \in Origin :
          DocumentTypeOK(Blob.wf[origin], origin)

TimerStorageTypeOK ==
    /\ BlobShapeOK
    /\ DeadlineOk

StorageTypeOK ==
    /\ WorkflowStorageTypeOK
    /\ TimerStorageTypeOK

C_TypeOK ==
    /\ now \in Time
    /\ StorageTypeOK
    /\ outbox \subseteq OutEntry
    /\ \A a, b \in outbox : MsgKey(a) = MsgKey(b) => a = b

ArmedTimers ==
    UNION { TimerNames(docs[o], o) : o \in Origin }

C_WheelSound ==
    DOMAIN timeouts \subseteq ArmedTimers

C_WheelComplete ==
    ArmedTimers \subseteq DOMAIN timeouts

SplitWrite ==
    \E r \in DOMAIN steps :
        /\ steps[r].phase = "perform"
        /\ docs[OriginOf(steps[r].ev)] /= steps[r].expect
        /\ \E j \in DOMAIN steps[r].pending :
               steps[r].pending[j].tag = "PutDocument"

NoSplitWrite ==
    ~SplitWrite

=============================================================================
