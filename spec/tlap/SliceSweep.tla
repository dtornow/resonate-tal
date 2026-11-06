----------------------------- MODULE SliceSweep -----------------------------
(* The slice recorded for a placed document is the store a sweep step
   starts from. Its image is already in the abstract closure. *)
EXTENDS SweepSent, PlantStep

LEMMA AppAt ==
    ASSUME NEW S, NEW e(_), NEW k \in S
    PROVE  [x \in S |-> e(x)][k] = e(k)
PROOF
    BY Z3, Isa

LEMMA ObjEta ==
    ASSUME NEW base,
           base = Objects
    PROVE  base = [ i \in DOMAIN base |-> base[i] ]
PROOF
    <1> DEFINE U == UNION { DOMAIN docs[p] : p \in Origin }
    <1>1. DOMAIN Objects = U
        BY DomCtor, Isa DEF Objects, U
    <1>2. ASSUME NEW i \in U
          PROVE  Objects[i] = docs[i.origin][i]
        BY <1>1, <1>2, AppAt, Isa DEF Objects, U
    <1>3. Objects = [ i \in U |-> docs[i.origin][i] ]
        BY Z3 DEF Objects, U
    <1>4. [ i \in U |-> docs[i.origin][i] ]
            = [ i \in DOMAIN Objects |-> Objects[i] ]
        BY <1>1, <1>2, ExtCtor
    <1>5. Objects = [ i \in DOMAIN Objects |-> Objects[i] ]
        BY <1>3, <1>4, Z3
    <1>6. QED
        BY <1>5, Z3

LEMMA SliceSweep ==
    ASSUME NEW o, NEW doc, NEW t,
           DOMAIN Objects \subseteq Id,
           DOMAIN doc = { i \in DOMAIN Objects : i.origin = o },
           \A i \in DOMAIN doc : Objects[i] = doc[i],
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address,
           \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id,
           \A k \in DOMAIN doc :
               \A a \in doc[k].promise.callbacks :
                   a \in DOMAIN Objects => a \in DOMAIN doc,
           t /= NoTime,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  Store(Plant(Objects, o, Sweep(doc, t).doc),
                 Deliver(outbox, Sweep(doc, t).sends)) \in P!Swept(t)
PROOF
    <1> DEFINE base == Objects
    <1>1. CbLocal(doc, base)
        BY Z3 DEF CbLocal, base
    <1>2. base = [ i \in DOMAIN base |-> base[i] ]
        BY ObjEta, Z3 DEF base
    <1>3. base = Objects
        BY Z3 DEF base
    <1>4. HIDE DEF Sweep, Plant, Deliver, Store
    <1>5. QED
        BY <1>1, <1>2, <1>3, SweepIn, Isa

(* Listener sends and retry sends are sequences, and the other passes send
   nothing, so the sweep's sends are a sequence. An empty tail drops. *)
LEMMA DropTail ==
    ASSUME NEW doc, NEW t, NEW b, DOMAIN doc \subseteq Id
    PROVE  /\ Sweep(doc, t).sends \o << >> = Sweep(doc, t).sends
           /\ Deliver(b, Sweep(doc, t).sends \o << >>)
                = Deliver(b, Sweep(doc, t).sends)
PROOF
    <1> DEFINE tdoc == SweepTimeoutAt(doc, t).doc
    <1> DEFINE edoc ==
            SweepExpiresAt(
                SweepCallbacks(SweepListeners(tdoc, t).doc, t).doc, t).doc
    <1> DEFINE P == DueN(tdoc, t)
    <1> DEFINE S ==
            { i \in DOMAIN edoc :
                edoc[i].task.state = "pending"
                /\ edoc[i].task.retryTimeoutAt <= t }
    <1>1. P = { x \in [id : { i \in DOMAIN tdoc :
                                tdoc[i].promise.state /= "pending" },
                       address : Address] :
                  x.address \in tdoc[x.id].promise.listeners }
        BY TimeoutDueN DEF tdoc, P
    <1>2. P = { x \in [id : { i \in DOMAIN SweepTimeoutAt(doc, t).doc :
                                SweepTimeoutAt(doc, t).doc[i].promise.state
                                  /= "pending" },
                       address : Address] :
                  x.address
                    \in SweepTimeoutAt(doc, t).doc[x.id].promise.listeners }
        BY <1>1 DEF tdoc
    <1>3. IsFiniteSet(P)
        BY <1>2, ListenDueFinite
    <1>4. S = { i \in DOMAIN SweepExpiresAt(
                            SweepCallbacks(
                                SweepListeners(
                                    SweepTimeoutAt(doc, t).doc, t).doc, t).doc,
                            t).doc :
                  /\ SweepExpiresAt(
                         SweepCallbacks(
                             SweepListeners(
                                 SweepTimeoutAt(doc, t).doc, t).doc, t).doc,
                         t).doc[i].task.state = "pending"
                  /\ SweepExpiresAt(
                         SweepCallbacks(
                             SweepListeners(
                                 SweepTimeoutAt(doc, t).doc, t).doc, t).doc,
                         t).doc[i].task.retryTimeoutAt <= t }
        BY Z3 DEF tdoc, edoc, S
    <1>5. IsFiniteSet(S)
        BY <1>4, RetryDueFinite
    <1>6. \E E : SweepListeners(tdoc, t).sends \in Seq(E)
        BY <1>1, <1>3, ListenSomeSeq, Isa
    <1>7. \E E : SweepRetryAt(edoc, t).sends \in Seq(E)
        BY <1>5, RetrySomeSeq, Isa DEF S
    <1>8. PICK E1 : SweepListeners(tdoc, t).sends \in Seq(E1)
        BY <1>6
    <1>9. PICK E2 : SweepRetryAt(edoc, t).sends \in Seq(E2)
        BY <1>7
    <1> DEFINE E1set == E1 \cup E2
    <1>10. E1 \subseteq E1set /\ E2 \subseteq E1set
        BY Z3 DEF E1set
    <1>11. SweepListeners(tdoc, t).sends \in Seq(E1set)
        BY <1>8, <1>10, SeqMonotonic
    <1>12. SweepRetryAt(edoc, t).sends \in Seq(E1set)
        BY <1>9, <1>10, SeqMonotonic
    <1> DEFINE heard == SweepListeners(tdoc, t).sends
    <1> DEFINE retried == SweepRetryAt(edoc, t).sends
    <1>13. heard = SweepListeners(SweepTimeoutAt(doc, t).doc, t).sends
        BY Isa DEF heard, tdoc
    <1>14. retried
            = SweepRetryAt(
                  SweepExpiresAt(
                      SweepCallbacks(
                          SweepListeners(
                              SweepTimeoutAt(doc, t).doc, t).doc, t).doc,
                      t).doc, t).sends
        BY Isa DEF retried, edoc, tdoc
    <1>15. Sweep(doc, t).sends = heard \o retried
        BY ONLY <1>11, <1>12, <1>13, <1>14, SweepSends, Isa
               DEF heard, retried, E1set
    <1>16. heard \o retried \in Seq(E1set)
        BY <1>11, <1>12, ConcatProperties DEF heard, retried
    <1>17. << >> \in Seq(E1set)
        BY EmptySeq DEF E1set
    <1>18. (heard \o retried) \o << >> = heard \o retried
        BY <1>16, <1>17, ConcatEmptySeq, Z3
    <1>19. Sweep(doc, t).sends \o << >> = Sweep(doc, t).sends
        BY ONLY <1>15, <1>18, Isa
    <1>20. HIDE DEF Deliver
    <1>21. QED
        BY <1>19, Z3

(* The perform write posts the sweep sends with an empty tail. Once the
   compared document's domain sits inside Id, that tail drops, so the
   outbox written is the outbox of the swept store. *)
LEMMA SweptBox ==
    ASSUME NEW o, NEW doc, NEW t, NEW sent,
           DOMAIN Objects \subseteq Id,
           DOMAIN doc = { i \in DOMAIN Objects : i.origin = o },
           \A i \in DOMAIN doc : Objects[i] = doc[i],
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address,
           \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id,
           \A k \in DOMAIN doc :
               \A a \in doc[k].promise.callbacks :
                   a \in DOMAIN Objects => a \in DOMAIN doc,
           t /= NoTime,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending",
           sent = Sweep(doc, t).sends \o << >>,
           outbox' = Deliver(outbox, sent),
           now' = now
    PROVE  LET pre == Store(Plant(Objects, o, Sweep(doc, t).doc),
                            Deliver(outbox, Sweep(doc, t).sends))
            IN  /\ pre \in P!Swept(t)
                /\ outbox' = pre.outbox
                /\ now' = now
PROOF
    <1> DEFINE pre ==
            Store(Plant(Objects, o, Sweep(doc, t).doc),
                  Deliver(outbox, Sweep(doc, t).sends))
    <1>1. DOMAIN doc \subseteq Id
        BY Z3
    <1>2. Deliver(outbox, Sweep(doc, t).sends \o << >>)
            = Deliver(outbox, Sweep(doc, t).sends)
        BY ONLY <1>1, DropTail, Isa
    <1>3. sent = Sweep(doc, t).sends \o << >>
        OBVIOUS
    <1>4. Deliver(outbox, sent) = Deliver(outbox, Sweep(doc, t).sends)
        BY ONLY <1>2, <1>3, Isa
    <1>5. pre \in P!Swept(t)
        BY SliceSweep, Isa DEF pre
    <1>6. HIDE DEF Sweep, Plant, Deliver
    <1>7. pre.outbox = Deliver(outbox, Sweep(doc, t).sends)
        BY ONLY Z3 DEF pre, Store
    <1>8. outbox' = pre.outbox
        BY <1>4, <1>7, Z3
    <1>9. QED
        BY <1>5, <1>8, Z3 DEF pre

(* The perform write replaces one origin. That is a plant of the handler
   document, and planting the swept document first does not change it. *)
LEMMA PlantedPut ==
    ASSUME NEW o \in Origin, NEW doc, NEW t, NEW body,
           DOMAIN docs = Origin,
           \A p \in Origin : \A i \in DOMAIN docs[p] : i.origin = p,
           \A i \in DOMAIN body : i.origin = o,
           \A i \in DOMAIN Sweep(doc, t).doc : i.origin = o,
           docs' = [docs EXCEPT ![o] = body]
    PROVE  LET mid == Sweep(doc, t).doc
                pre == Store(Plant(Objects, o, mid),
                             Deliver(outbox, Sweep(doc, t).sends))
            IN  Objects' = Plant(pre.objects, o, body)
PROOF
    <1> DEFINE mid == Sweep(doc, t).doc
    <1> DEFINE pre ==
            Store(Plant(Objects, o, mid),
                  Deliver(outbox, Sweep(doc, t).sends))
    <1>1. o \in Origin
        OBVIOUS
    <1>2. DOMAIN docs = Origin
        OBVIOUS
    <1>3. \A p \in Origin : \A i \in DOMAIN docs[p] : i.origin = p
        OBVIOUS
    <1>4. \A i \in DOMAIN body : i.origin = o
        OBVIOUS
    <1>5. docs' = [docs EXCEPT ![o] = body]
        OBVIOUS
    <1>6. Obj([docs EXCEPT ![o] = body]) = Plant(Obj(docs), o, body)
        BY ONLY <1>1, <1>2, <1>3, <1>4, PlantFun, Isa
    <1>7. Objects = Obj(docs) /\ Objects' = Obj(docs')
        BY ONLY ObjectsAre, Z3
    <1>8. Objects' = Plant(Objects, o, body)
        BY ONLY <1>5, <1>6, <1>7, Isa
    <1>9. \A i \in DOMAIN mid : i.origin = o
        BY Z3 DEF mid
    <1>10. Plant(Plant(Objects, o, mid), o, body) = Plant(Objects, o, body)
        BY ONLY <1>4, <1>9, PlantTwice, Isa
    <1>11. HIDE DEF Sweep, Plant, Deliver
    <1>12. pre.objects = Plant(Objects, o, mid)
        BY ONLY Z3 DEF pre, Store, mid
    <1>13. QED
        BY ONLY <1>8, <1>10, <1>12, Isa DEF pre, mid

(* A disabled settle leaves the origin document, so planting it is the
   identity. An enabled settle returns the planted document, and that store
   is in the abstract handler set. *)
LEMMA SettleSkip ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ],
           P!HandlePromiseSettle(base, req, t) = {}
    PROVE  Plant(base, o, HandlePromiseSettle(req, doc, t).doc) = base
PROOF
    <1> DEFINE c == HandlePromiseSettle(req, doc, t)
    <1> DEFINE a == P!HandlePromiseSettle(base, req, t)
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
        BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5, SettleLift, Isa DEF c, a
    <1>7. Plant(base, o, doc) = base
        BY ONLY <1>1, <1>2, <1>4, PlantId, Isa
    <1>8. QED
        BY ONLY <1>6, <1>7, Isa DEF c

LEMMA SettleMem ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t, NEW planted,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ],
           req \in SettleReq,
           P!HandlePromiseSettle(base, req, t) # {},
           planted = Plant(base, o, HandlePromiseSettle(req, doc, t).doc)
    PROVE  planted \in P!Handled(base, t)
PROOF
    <1> DEFINE c == HandlePromiseSettle(req, doc, t)
    <1> DEFINE a == P!HandlePromiseSettle(base, req, t)
    <1>1. DOMAIN doc = { i \in DOMAIN base : i.origin = o }
        OBVIOUS
    <1>2. \A i \in DOMAIN doc : base[i] = doc[i]
        OBVIOUS
    <1>3. req.id.origin = o
        OBVIOUS
    <1>4. base = [ i \in DOMAIN base |-> base[i] ]
        OBVIOUS
    <1>5. req \in SettleReq
        OBVIOUS
    <1>6. planted = Plant(base, o, HandlePromiseSettle(req, doc, t).doc)
        OBVIOUS
    <1>7. a # {}
        BY Z3 DEF a
    <1>8. c = HandlePromiseSettle(req, doc, t)
        BY Z3 DEF c
    <1>9. IF a = {} THEN c.doc = doc ELSE a = {Plant(base, o, c.doc)}
        <2>1. ASSUME NEW rr, rr = req, rr.id.origin = o
              PROVE  LET u == HandlePromiseSettle(rr, doc, t)
                          v == P!HandlePromiseSettle(base, rr, t)
                      IN  IF v = {} THEN u.doc = doc
                          ELSE v = {Plant(base, o, u.doc)}
            BY <2>1, SettleLift
        <2>2. QED
            BY <1>3, <1>8, <2>1, Zenon DEF c, a
    <1>5a. req \in P!SettleReq
        BY ONLY <1>5, SameSettle, Z3
    <1> DEFINE p == Plant(base, o, c.doc)
    <1> DEFINE S == { P!HandlePromiseSettle(base, r, t) : r \in P!SettleReq }
    <1>10. p = Plant(base, o, c.doc)
        BY Z3 DEF p
    <1>11. p = planted
        BY ONLY <1>6, <1>8, <1>10, Isa
    <1>12. a = {p}
        BY ONLY <1>7, <1>9, Z3 DEF p
    <1>13. p \in a
        BY <1>12, Z3
    <1>14. a \in { P!HandlePromiseSettle(base, r, t) : r \in P!SettleReq }
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

(* A disabled create leaves the origin document. An enabled create returns
   the planted document, which the abstract handler set contains. *)
LEMMA CreateSkip ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ],
           P!HandlePromiseCreate(base, req, t) = {}
    PROVE  Plant(base, o, HandlePromiseCreate(req, doc, t).doc) = base
PROOF
    <1> DEFINE c == HandlePromiseCreate(req, doc, t)
    <1> DEFINE a == P!HandlePromiseCreate(base, req, t)
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
        BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5, CreateLift, Isa DEF c, a
    <1>7. Plant(base, o, doc) = base
        BY ONLY <1>1, <1>2, <1>4, PlantId, Isa
    <1>8. QED
        BY ONLY <1>6, <1>7, Isa DEF c

LEMMA CreateMem ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t, NEW planted,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ],
           req \in CreateReq,
           P!HandlePromiseCreate(base, req, t) # {},
           planted = Plant(base, o, HandlePromiseCreate(req, doc, t).doc)
    PROVE  planted \in P!Handled(base, t)
PROOF
    <1> DEFINE c == HandlePromiseCreate(req, doc, t)
    <1> DEFINE a == P!HandlePromiseCreate(base, req, t)
    <1>1. DOMAIN doc = { i \in DOMAIN base : i.origin = o }
        OBVIOUS
    <1>2. \A i \in DOMAIN doc : base[i] = doc[i]
        OBVIOUS
    <1>3. req.id.origin = o
        OBVIOUS
    <1>4. base = [ i \in DOMAIN base |-> base[i] ]
        OBVIOUS
    <1>5. req \in CreateReq
        OBVIOUS
    <1>6. planted = Plant(base, o, HandlePromiseCreate(req, doc, t).doc)
        OBVIOUS
    <1>7. a # {}
        BY Z3 DEF a
    <1>8. c = HandlePromiseCreate(req, doc, t)
        BY Z3 DEF c
    <1>9. IF a = {} THEN c.doc = doc ELSE a = {Plant(base, o, c.doc)}
        <2>1. ASSUME NEW rr, rr = req, rr.id.origin = o
              PROVE  LET u == HandlePromiseCreate(rr, doc, t)
                          v == P!HandlePromiseCreate(base, rr, t)
                      IN  IF v = {} THEN u.doc = doc
                          ELSE v = {Plant(base, o, u.doc)}
            BY <2>1, CreateLift
        <2>2. QED
            BY <1>3, <1>8, <2>1, Zenon DEF c, a
    <1>5a. req \in P!CreateReq
        BY ONLY <1>5, SameCreate, Z3
    <1> DEFINE p == Plant(base, o, c.doc)
    <1> DEFINE S == { P!HandlePromiseCreate(base, r, t) : r \in P!CreateReq }
    <1>10. p = Plant(base, o, c.doc)
        BY Z3 DEF p
    <1>11. p = planted
        BY ONLY <1>6, <1>8, <1>10, Isa
    <1>12. a = {p}
        BY ONLY <1>7, <1>9, Z3 DEF p
    <1>13. p \in a
        BY <1>12, Z3
    <1>14. a \in { P!HandlePromiseCreate(base, r, t) : r \in P!CreateReq }
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
