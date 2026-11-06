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

=============================================================================
