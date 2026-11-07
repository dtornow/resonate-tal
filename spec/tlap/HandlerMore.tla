------------------------------ MODULE HandlerMore ------------------------------
(* Remaining concrete handler writes, planted into the swept store, are
   either the identity or one of the abstract Handled states. *)
EXTENDS SliceSweep

LEMMA SameAcquire ==
    [id : Id, version : Version, pid : Pid, ttl : Ttl]
        = [id : P!Id, version : P!Version, pid : Pid, ttl : Ttl]
PROOF
    BY SameId, SameVersion DEF Id, P!Id, Version, P!Version

LEMMA AcquireSkip ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ],
           P!HandleTaskAcquire(base, req, t) = {}
    PROVE  Plant(base, o, HandleTaskAcquire(req, doc, t).doc) = base
PROOF
    <1> DEFINE c == HandleTaskAcquire(req, doc, t)
    <1> DEFINE a == P!HandleTaskAcquire(base, req, t)
    <1>1. DOMAIN doc = { i \in DOMAIN base : i.origin = o }
        OBVIOUS
    <1>2. \A i \in DOMAIN doc : base[i] = doc[i]
        OBVIOUS
    <1>3. req.id.origin = o
        OBVIOUS
    <1>4. base = [ i \in DOMAIN base |-> base[i] ]
        OBVIOUS
    <1>5. a = {}
        BY Z3 DEF a
    <1>6. c.doc = doc
        BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5, AcquireLift, Isa DEF c, a
    <1>7. Plant(base, o, doc) = base
        BY ONLY <1>1, <1>2, <1>4, PlantId, Isa
    <1>8. QED
        BY ONLY <1>6, <1>7, Isa DEF c

LEMMA AcquireMem ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t, NEW planted,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ],
           req \in [id : Id, version : Version, pid : Pid, ttl : Ttl],
           P!HandleTaskAcquire(base, req, t) # {},
           planted = Plant(base, o, HandleTaskAcquire(req, doc, t).doc)
    PROVE  planted \in P!Handled(base, t)
PROOF
    <1> DEFINE c == HandleTaskAcquire(req, doc, t)
    <1> DEFINE a == P!HandleTaskAcquire(base, req, t)
    <1>1. DOMAIN doc = { i \in DOMAIN base : i.origin = o }
        OBVIOUS
    <1>2. \A i \in DOMAIN doc : base[i] = doc[i]
        OBVIOUS
    <1>3. req.id.origin = o
        OBVIOUS
    <1>4. base = [ i \in DOMAIN base |-> base[i] ]
        OBVIOUS
    <1>5. req \in [id : Id, version : Version, pid : Pid, ttl : Ttl]
        OBVIOUS
    <1>6. planted = Plant(base, o, HandleTaskAcquire(req, doc, t).doc)
        OBVIOUS
    <1>7. a # {}
        BY Z3 DEF a
    <1>8. c = HandleTaskAcquire(req, doc, t)
        BY Z3 DEF c
    <1>9. IF a = {} THEN c.doc = doc ELSE a = {Plant(base, o, c.doc)}
        <2>1. ASSUME NEW rr, rr = req, rr.id.origin = o
              PROVE  LET u == HandleTaskAcquire(rr, doc, t)
                          v == P!HandleTaskAcquire(base, rr, t)
                      IN  IF v = {} THEN u.doc = doc
                          ELSE v = {Plant(base, o, u.doc)}
            BY <2>1, AcquireLift
        <2>2. QED
            BY <1>3, <1>8, <2>1, Zenon DEF c, a
    <1>5a. req \in [id : P!Id, version : P!Version, pid : Pid, ttl : Ttl]
        BY ONLY <1>5, SameAcquire, Z3
    <1> DEFINE p == Plant(base, o, c.doc)
    <1> DEFINE S == { P!HandleTaskAcquire(base, r, t) :
                        r \in [id : P!Id, version : P!Version,
                              pid : Pid, ttl : Ttl] }
    <1>10. p = Plant(base, o, c.doc)
        BY Z3 DEF p
    <1>11. p = planted
        BY ONLY <1>6, <1>8, <1>10, Isa
    <1>12. a = {p}
        BY ONLY <1>7, <1>9, Z3 DEF p
    <1>13. p \in a
        BY <1>12, Z3
    <1>14. a \in { P!HandleTaskAcquire(base, r, t) :
                     r \in [id : P!Id, version : P!Version,
                           pid : Pid, ttl : Ttl] }
        BY <1>5a, Z3, IsaM("blast") DEF a
    <1>15. a \in S /\ S # {}
        BY <1>14, Z3 DEF S
    <1>16. P!Flat(S) = UNION S
        BY <1>15, Z3 DEF P!Flat, S
    <1>17. p \in P!Flat(S)
        BY <1>13, <1>15, <1>16, Z3
    <1>18. HIDE DEF P!HandlePromiseCreate, P!HandlePromiseSettle,
                P!HandlePromiseRegisterCallback,
                P!HandlePromiseRegisterListener,
                P!HandleTaskCreate, P!HandleTaskAcquire,
                P!HandleTaskFence, P!HandleTaskHeartbeat,
                P!HandleTaskSuspend, P!HandleTaskFulfill,
                P!HandleTaskRelease, P!HandleTaskHalt,
                P!HandleTaskContinue
    <1>19. P!Flat(S) \subseteq P!Handled(base, t)
        BY ONLY <1>15, Z3, Isa DEF S, P!Handled, P!Flat
    <1>20. p \in P!Handled(base, t)
        BY <1>17, <1>19, Z3
    <1>21. QED
        BY <1>11, <1>20, Z3

LEMMA SameTaskCreate ==
    [pid : Pid, ttl : Ttl, action : CreateReq]
        = [pid : Pid, ttl : Ttl, action : P!CreateReq]
PROOF
    BY SameCreate DEF CreateReq, P!CreateReq

LEMMA TaskCreateSkip ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.action.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ],
           P!HandleTaskCreate(base, req, t) = {}
    PROVE  Plant(base, o, HandleTaskCreate(req, doc, t).doc) = base
PROOF
    <1> DEFINE c == HandleTaskCreate(req, doc, t)
    <1> DEFINE a == P!HandleTaskCreate(base, req, t)
    <1>1. DOMAIN doc = { i \in DOMAIN base : i.origin = o }
        OBVIOUS
    <1>2. \A i \in DOMAIN doc : base[i] = doc[i]
        OBVIOUS
    <1>3. req.action.id.origin = o
        OBVIOUS
    <1>4. base = [ i \in DOMAIN base |-> base[i] ]
        OBVIOUS
    <1>5. a = {}
        BY Z3 DEF a
    <1>6. c.doc = doc
        BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5, TaskCreateLift, Isa DEF c, a
    <1>7. Plant(base, o, doc) = base
        BY ONLY <1>1, <1>2, <1>4, PlantId, Isa
    <1>8. QED
        BY ONLY <1>6, <1>7, Isa DEF c

LEMMA TaskCreateMem ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t, NEW planted,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.action.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ],
           req \in [pid : Pid, ttl : Ttl, action : CreateReq],
           P!HandleTaskCreate(base, req, t) # {},
           planted = Plant(base, o, HandleTaskCreate(req, doc, t).doc)
    PROVE  planted \in P!Handled(base, t)
PROOF
    <1> DEFINE c == HandleTaskCreate(req, doc, t)
    <1> DEFINE a == P!HandleTaskCreate(base, req, t)
    <1>1. DOMAIN doc = { i \in DOMAIN base : i.origin = o }
        OBVIOUS
    <1>2. \A i \in DOMAIN doc : base[i] = doc[i]
        OBVIOUS
    <1>3. req.action.id.origin = o
        OBVIOUS
    <1>4. base = [ i \in DOMAIN base |-> base[i] ]
        OBVIOUS
    <1>5. req \in [pid : Pid, ttl : Ttl, action : CreateReq]
        OBVIOUS
    <1>6. planted = Plant(base, o, HandleTaskCreate(req, doc, t).doc)
        OBVIOUS
    <1>7. a # {}
        BY Z3 DEF a
    <1>8. c = HandleTaskCreate(req, doc, t)
        BY Z3 DEF c
    <1>9. IF a = {} THEN c.doc = doc ELSE a = {Plant(base, o, c.doc)}
        <2>1. ASSUME NEW rr, rr = req, rr.action.id.origin = o
              PROVE  LET u == HandleTaskCreate(rr, doc, t)
                          v == P!HandleTaskCreate(base, rr, t)
                      IN  IF v = {} THEN u.doc = doc
                          ELSE v = {Plant(base, o, u.doc)}
            BY <2>1, TaskCreateLift
        <2>2. QED
            BY <1>3, <1>8, <2>1, Zenon DEF c, a
    <1>5a. req \in [pid : Pid, ttl : Ttl, action : P!CreateReq]
        BY ONLY <1>5, SameTaskCreate, Z3
    <1> DEFINE p == Plant(base, o, c.doc)
    <1> DEFINE S == { P!HandleTaskCreate(base, r, t) :
                        r \in [pid : Pid, ttl : Ttl, action : P!CreateReq] }
    <1>10. p = Plant(base, o, c.doc)
        BY Z3 DEF p
    <1>11. p = planted
        BY ONLY <1>6, <1>8, <1>10, Isa
    <1>12. a = {p}
        BY ONLY <1>7, <1>9, Z3 DEF p
    <1>13. p \in a
        BY <1>12, Z3
    <1>14. a \in { P!HandleTaskCreate(base, r, t) :
                     r \in [pid : Pid, ttl : Ttl, action : P!CreateReq] }
        BY <1>5a, Z3, IsaM("blast") DEF a
    <1>15. a \in S /\ S # {}
        BY <1>14, Z3 DEF S
    <1>16. P!Flat(S) = UNION S
        BY <1>15, Z3 DEF P!Flat, S
    <1>17. p \in P!Flat(S)
        BY <1>13, <1>15, <1>16, Z3
    <1>18. HIDE DEF P!HandlePromiseCreate, P!HandlePromiseSettle,
                P!HandlePromiseRegisterCallback,
                P!HandlePromiseRegisterListener,
                P!HandleTaskCreate, P!HandleTaskAcquire,
                P!HandleTaskFence, P!HandleTaskHeartbeat,
                P!HandleTaskSuspend, P!HandleTaskFulfill,
                P!HandleTaskRelease, P!HandleTaskHalt,
                P!HandleTaskContinue
    <1>19. P!Flat(S) \subseteq P!Handled(base, t)
        BY ONLY <1>15, Z3, Isa DEF S, P!Handled, P!Flat
    <1>20. p \in P!Handled(base, t)
        BY <1>17, <1>19, Z3
    <1>21. QED
        BY <1>11, <1>20, Z3

LEMMA SameSuspend ==
    [id : Id, version : Version, actions : SUBSET CallbackReq]
        = [id : P!Id, version : P!Version, actions : SUBSET P!CallbackReq]
PROOF
    BY SameId, SameVersion, SameCallback
       DEF Id, P!Id, Version, P!Version, CallbackReq, P!CallbackReq

LEMMA SuspendSkip ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ],
           P!HandleTaskSuspend(base, req, t) = {}
    PROVE  Plant(base, o, HandleTaskSuspend(req, doc, t).doc) = base
PROOF
    <1> DEFINE c == HandleTaskSuspend(req, doc, t)
    <1> DEFINE a == P!HandleTaskSuspend(base, req, t)
    <1>1. DOMAIN doc = { i \in DOMAIN base : i.origin = o }
        OBVIOUS
    <1>2. \A i \in DOMAIN doc : base[i] = doc[i]
        OBVIOUS
    <1>3. req.id.origin = o
        OBVIOUS
    <1>4. base = [ i \in DOMAIN base |-> base[i] ]
        OBVIOUS
    <1>5. a = {}
        BY Z3 DEF a
    <1>6. c.doc = doc
        BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5, SuspendLift, Isa DEF c, a
    <1>7. Plant(base, o, doc) = base
        BY ONLY <1>1, <1>2, <1>4, PlantId, Isa
    <1>8. QED
        BY ONLY <1>6, <1>7, Isa DEF c

LEMMA SuspendMem ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t, NEW planted,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ],
           req \in [id : Id, version : Version, actions : SUBSET CallbackReq],
           P!HandleTaskSuspend(base, req, t) # {},
           planted = Plant(base, o, HandleTaskSuspend(req, doc, t).doc)
    PROVE  planted \in P!Handled(base, t)
PROOF
    <1> DEFINE c == HandleTaskSuspend(req, doc, t)
    <1> DEFINE a == P!HandleTaskSuspend(base, req, t)
    <1>1. DOMAIN doc = { i \in DOMAIN base : i.origin = o }
        OBVIOUS
    <1>2. \A i \in DOMAIN doc : base[i] = doc[i]
        OBVIOUS
    <1>3. req.id.origin = o
        OBVIOUS
    <1>4. base = [ i \in DOMAIN base |-> base[i] ]
        OBVIOUS
    <1>5. req \in [id : Id, version : Version, actions : SUBSET CallbackReq]
        OBVIOUS
    <1>6. planted = Plant(base, o, HandleTaskSuspend(req, doc, t).doc)
        OBVIOUS
    <1>7. a # {}
        BY Z3 DEF a
    <1>8. c = HandleTaskSuspend(req, doc, t)
        BY Z3 DEF c
    <1>9. IF a = {} THEN c.doc = doc ELSE a = {Plant(base, o, c.doc)}
        <2>1. ASSUME NEW rr, rr = req, rr.id.origin = o
              PROVE  LET u == HandleTaskSuspend(rr, doc, t)
                          v == P!HandleTaskSuspend(base, rr, t)
                      IN  IF v = {} THEN u.doc = doc
                          ELSE v = {Plant(base, o, u.doc)}
            BY <2>1, SuspendLift
        <2>2. QED
            BY <1>3, <1>8, <2>1, Zenon DEF c, a
    <1>5a. req \in [id : P!Id, version : P!Version,
                     actions : SUBSET P!CallbackReq]
        BY ONLY <1>5, SameSuspend, Z3
    <1> DEFINE p == Plant(base, o, c.doc)
    <1> DEFINE S == { P!HandleTaskSuspend(base, r, t) :
                        r \in [id : P!Id, version : P!Version,
                              actions : SUBSET P!CallbackReq] }
    <1>10. p = Plant(base, o, c.doc)
        BY Z3 DEF p
    <1>11. p = planted
        BY ONLY <1>6, <1>8, <1>10, Isa
    <1>12. a = {p}
        BY ONLY <1>7, <1>9, Z3 DEF p
    <1>13. p \in a
        BY <1>12, Z3
    <1>14. a \in { P!HandleTaskSuspend(base, r, t) :
                     r \in [id : P!Id, version : P!Version,
                           actions : SUBSET P!CallbackReq] }
        BY <1>5a, Z3, IsaM("blast") DEF a
    <1>15. a \in S /\ S # {}
        BY <1>14, Z3 DEF S
    <1>16. P!Flat(S) = UNION S
        BY <1>15, Z3 DEF P!Flat, S
    <1>17. p \in P!Flat(S)
        BY <1>13, <1>15, <1>16, Z3
    <1>18. HIDE DEF P!HandlePromiseCreate, P!HandlePromiseSettle,
                P!HandlePromiseRegisterCallback,
                P!HandlePromiseRegisterListener,
                P!HandleTaskCreate, P!HandleTaskAcquire,
                P!HandleTaskFence, P!HandleTaskHeartbeat,
                P!HandleTaskSuspend, P!HandleTaskFulfill,
                P!HandleTaskRelease, P!HandleTaskHalt,
                P!HandleTaskContinue
    <1>19. P!Flat(S) \subseteq P!Handled(base, t)
        BY ONLY <1>15, Z3, Isa DEF S, P!Handled, P!Flat
    <1>20. p \in P!Handled(base, t)
        BY <1>17, <1>19, Z3
    <1>21. QED
        BY <1>11, <1>20, Z3

(* Fence and heartbeat are nondeterministic abstract handlers, so their lift
   lemmas classify a concrete write directly as identity or Handled. *)
LEMMA FenceClass ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t, NEW planted,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           req.id \in Id,
           req.version \in Version,
           req.action \in FenceAction,
           base = [ i \in DOMAIN base |-> base[i] ],
           planted = Plant(base, o, HandleTaskFence(req, doc, t).doc)
    PROVE  planted = base \/ planted \in P!Handled(base, t)
PROOF
    <1> DEFINE c == HandleTaskFence(req, doc, t)
    <1> DEFINE a == P!HandleTaskFence(base, req.id, req.version, t)
    <1>1. DOMAIN doc = { i \in DOMAIN base : i.origin = o }
        OBVIOUS
    <1>2. \A i \in DOMAIN doc : base[i] = doc[i]
        OBVIOUS
    <1>3. req.id.origin = o
        OBVIOUS
    <1>4. req.id \in Id
        OBVIOUS
    <1>5. req.version \in Version
        OBVIOUS
    <1>6. req.action \in FenceAction
        OBVIOUS
    <1>7. base = [ i \in DOMAIN base |-> base[i] ]
        OBVIOUS
    <1>8. planted = Plant(base, o, c.doc)
        BY Z3 DEF c
    <1>9. c.doc = doc \/ Plant(base, o, c.doc) \in a
        <2>1. ASSUME NEW rr, rr = req, rr.id.origin = o,
                      rr.action \in FenceAction
              PROVE  LET u == HandleTaskFence(rr, doc, t)
                          v == P!HandleTaskFence(base, rr.id, rr.version, t)
                      IN  u.doc = doc \/ Plant(base, o, u.doc) \in v
            BY <2>1, FenceLift
        <2>2. QED
            BY <1>3, <1>6, <2>1, Zenon DEF c, a
    <1>10. CASE c.doc = doc
        <2>1. Plant(base, o, doc) = base
            BY ONLY <1>1, <1>2, <1>7, PlantId, Isa
        <2>2. planted = base
            BY ONLY <1>8, <1>10, <2>1, Isa
        <2>3. QED
            BY <2>2
    <1>11. CASE Plant(base, o, c.doc) \in a
        <2>1. req.id \in P!Id
            BY ONLY <1>4, SameId, Z3
        <2>2. req.version \in P!Version
            BY ONLY <1>5, SameVersion, Z3
        <2> DEFINE p == Plant(base, o, c.doc)
        <2> DEFINE S == { P!HandleTaskFence(base, i, v, t) :
                            i \in P!Id, v \in P!Version }
        <2>3. p \in a
            BY <1>11 DEF p
        <2>4. a \in { P!HandleTaskFence(base, i, v, t) :
                        i \in P!Id, v \in P!Version }
            BY <2>1, <2>2, Z3, IsaM("blast") DEF a
        <2>5. a \in S /\ S # {}
            BY <2>4, Z3 DEF S
        <2>6. P!Flat(S) = UNION S
            BY <2>5, Z3 DEF P!Flat, S
        <2>7. p \in P!Flat(S)
            BY <2>3, <2>5, <2>6, Z3
        <2>8. HIDE DEF P!HandlePromiseCreate, P!HandlePromiseSettle,
                    P!HandlePromiseRegisterCallback,
                    P!HandlePromiseRegisterListener,
                    P!HandleTaskCreate, P!HandleTaskAcquire,
                    P!HandleTaskFence, P!HandleTaskHeartbeat,
                    P!HandleTaskSuspend, P!HandleTaskFulfill,
                    P!HandleTaskRelease, P!HandleTaskHalt,
                    P!HandleTaskContinue
        <2>9. P!Flat(S) \subseteq P!Handled(base, t)
            BY ONLY <2>5, Z3, Isa DEF S, P!Handled, P!Flat
        <2>10. p \in P!Handled(base, t)
            BY <2>7, <2>9, Z3
        <2>11. planted \in P!Handled(base, t)
            BY ONLY <1>8, <2>10, Isa DEF p
        <2>12. QED
            BY <2>11
    <1>12. QED
        BY <1>9, <1>10, <1>11

LEMMA SameHeartbeat ==
    [pid : Pid, tasks : SUBSET TaskRefT]
        = [pid : Pid, tasks : SUBSET P!TaskRefT]
PROOF
    BY SameTaskRef DEF TaskRefT, P!TaskRefT

LEMMA HeartbeatClass ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t, NEW planted,
           o \in Origin,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           base = [ i \in DOMAIN base |-> base[i] ],
           req \in [pid : Pid, tasks : SUBSET TaskRefT],
           planted = Plant(base, o, HandleTaskHeartbeat(req, doc, t).doc)
    PROVE  planted = base \/ planted \in P!Handled(base, t)
PROOF
    <1> DEFINE c == HandleTaskHeartbeat(req, doc, t)
    <1> DEFINE a == P!HandleTaskHeartbeat(base, req, t)
    <1>1. o \in Origin
        OBVIOUS
    <1>2. DOMAIN doc = { i \in DOMAIN base : i.origin = o }
        OBVIOUS
    <1>3. \A i \in DOMAIN doc : base[i] = doc[i]
        OBVIOUS
    <1>4. base = [ i \in DOMAIN base |-> base[i] ]
        OBVIOUS
    <1>5. req \in [pid : Pid, tasks : SUBSET TaskRefT]
        OBVIOUS
    <1>6. planted = Plant(base, o, c.doc)
        BY Z3 DEF c
    <1>7. IF a = {} THEN c.doc = doc
          ELSE Plant(base, o, c.doc) \in a
        <2>1. ASSUME NEW rr, rr = req, NEW oo, oo = o, oo \in Origin
              PROVE  LET u == HandleTaskHeartbeat(rr, doc, t)
                          v == P!HandleTaskHeartbeat(base, rr, t)
                      IN  IF v = {} THEN u.doc = doc
                          ELSE Plant(base, oo, u.doc) \in v
            BY <2>1, HeartbeatLift
        <2>2. QED
            BY <1>1, <2>1, Zenon DEF c, a
    <1>8. CASE a = {}
        <2>1. c.doc = doc
            BY <1>7, <1>8
        <2>2. Plant(base, o, doc) = base
            BY ONLY <1>2, <1>3, <1>4, PlantId, Isa
        <2>3. planted = base
            BY ONLY <1>6, <2>1, <2>2, Isa
        <2>4. QED
            BY <2>3
    <1>9. CASE a # {}
        <2>1. req \in [pid : Pid, tasks : SUBSET P!TaskRefT]
            BY ONLY <1>5, SameHeartbeat, Z3
        <2> DEFINE p == Plant(base, o, c.doc)
        <2> DEFINE S == { P!HandleTaskHeartbeat(base, r, t) :
                            r \in [pid : Pid, tasks : SUBSET P!TaskRefT] }
        <2>2. p \in a
            BY <1>7, <1>9 DEF p
        <2>3. a \in { P!HandleTaskHeartbeat(base, r, t) :
                        r \in [pid : Pid, tasks : SUBSET P!TaskRefT] }
            BY <2>1, Z3, IsaM("blast") DEF a
        <2>4. a \in S /\ S # {}
            BY <2>3, Z3 DEF S
        <2>5. P!Flat(S) = UNION S
            BY <2>4, Z3 DEF P!Flat, S
        <2>6. p \in P!Flat(S)
            BY <2>2, <2>4, <2>5, Z3
        <2>7. HIDE DEF P!HandlePromiseCreate, P!HandlePromiseSettle,
                    P!HandlePromiseRegisterCallback,
                    P!HandlePromiseRegisterListener,
                    P!HandleTaskCreate, P!HandleTaskAcquire,
                    P!HandleTaskFence, P!HandleTaskHeartbeat,
                    P!HandleTaskSuspend, P!HandleTaskFulfill,
                    P!HandleTaskRelease, P!HandleTaskHalt,
                    P!HandleTaskContinue
        <2>8. P!Flat(S) \subseteq P!Handled(base, t)
            BY ONLY <2>4, Z3, Isa DEF S, P!Handled, P!Flat
        <2>9. p \in P!Handled(base, t)
            BY <2>6, <2>8, Z3
        <2>10. planted \in P!Handled(base, t)
            BY ONLY <1>6, <2>9, Isa DEF p
        <2>11. QED
            BY <2>10
    <1>10. QED
        BY <1>8, <1>9

=============================================================================
