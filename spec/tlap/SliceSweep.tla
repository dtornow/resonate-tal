----------------------------- MODULE SliceSweep -----------------------------
(* The slice recorded for a placed document is the store a sweep step
   starts from. Its image is already in the abstract closure. *)
EXTENDS SweepSent

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

=============================================================================
