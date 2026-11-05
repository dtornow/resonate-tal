----------------------------- MODULE ApplyStep -----------------------------
(* A placed origin document is the slice of the store. The sweep closure
   is stated on that slice; this lemma only records the slice. *)
EXTENDS PlaceJoin

LEMMA OriginSlice ==
    ASSUME Placed, NEW o \in Origin
    PROVE  LET doc == docs[o]
            IN  /\ DOMAIN Objects \subseteq Id
                /\ DOMAIN doc = { i \in DOMAIN Objects : i.origin = o }
                /\ \A i \in DOMAIN doc : Objects[i] = doc[i]
                /\ \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address
                /\ \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id
                /\ \A k \in DOMAIN doc :
                      \A a \in doc[k].promise.callbacks :
                          a \in DOMAIN Objects => a \in DOMAIN doc
                /\ \A k \in DOMAIN doc :
                      doc[k].task.state = "acquired" =>
                        /\ doc[k].task.leaseTimeoutAt /= NoTime
                        /\ doc[k].promise.state = "pending"
                /\ \A k \in DOMAIN doc :
                      doc[k].task.state = "pending" =>
                        /\ doc[k].task.retryTimeoutAt /= NoTime
                        /\ doc[k].promise.state = "pending"
                /\ \A k \in DOMAIN doc :
                      doc[k].task.state = "suspended" =>
                        doc[k].promise.state = "pending"
PROOF
    <1> DEFINE doc == docs[o]
    <1> DEFINE U == UNION { DOMAIN docs[p] : p \in Origin }
    <1>1. DOMAIN docs = Origin /\ DocOk(doc) /\ Home(doc, o)
        BY Z3 DEF Placed, doc
    <1>2. DOMAIN doc \subseteq { i \in Id : i.origin = o }
        BY <1>1 DEF Home, doc
    <1>3. DOMAIN Objects = UNION { DOMAIN docs[q] : q \in Origin }
        BY DomCtor, Isa DEF Objects
    <1>4. U = UNION { DOMAIN docs[q] : q \in Origin }
        BY Z3 DEF U
    <1>5. DOMAIN Objects = U
        BY <1>3, <1>4, Z3
    <1>6. ASSUME NEW p \in Origin
          PROVE  \A i \in DOMAIN docs[p] : i.origin = p /\ i \in Id
        <2>1. Home(docs[p], p)
            BY <1>6 DEF Placed
        <2>2. QED
            BY <2>1 DEF Home
    <1>7. U \subseteq Id
        BY <1>6, Z3 DEF U
    <1>8. DOMAIN Objects \subseteq Id
        BY <1>5, <1>7, Z3
    <1>9. ASSUME NEW i \in U
          PROVE  Objects[i] = docs[i.origin][i]
        BY <1>5, <1>9, AppCtor, Isa DEF Objects, U
    <1>10. \A i \in DOMAIN doc : i \in U /\ i.origin = o /\ Objects[i] = doc[i]
        BY <1>1, <1>2, <1>9, Z3 DEF doc, U
    <1>11. { i \in DOMAIN Objects : i.origin = o } \subseteq DOMAIN doc
        BY <1>5, <1>6, Z3 DEF doc, U
    <1>12. DOMAIN doc \subseteq { i \in DOMAIN Objects : i.origin = o }
        BY <1>5, <1>10, Z3
    <1>13. DOMAIN doc = { i \in DOMAIN Objects : i.origin = o }
        BY <1>11, <1>12, Z3
    <1>14. \A i \in DOMAIN doc : Objects[i] = doc[i]
        BY <1>10, Z3
    <1>15. \A k \in DOMAIN doc :
              /\ doc[k].promise.callbacks \subseteq DOMAIN doc
              /\ doc[k].promise.listeners \subseteq Address
              /\ (doc[k].task.state = "acquired" =>
                    /\ doc[k].task.leaseTimeoutAt /= NoTime
                    /\ doc[k].task.ttl \in Ttl
                    /\ doc[k].promise.state = "pending")
              /\ (doc[k].task.state = "pending" =>
                    /\ doc[k].task.retryTimeoutAt /= NoTime
                    /\ doc[k].promise.state = "pending")
              /\ (doc[k].task.state = "suspended" =>
                    doc[k].promise.state = "pending")
        BY <1>1 DEF doc, DocOk, Guard
    <1>16. \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id
        BY <1>2, <1>15, Z3
    <1>17. \A k \in DOMAIN doc :
              \A a \in doc[k].promise.callbacks :
                  a \in DOMAIN Objects => a \in DOMAIN doc
        BY <1>15, Z3
    <1>18. QED
        BY <1>8, <1>13, <1>14, <1>15, <1>16, <1>17, Z3 DEF doc

(* A handler posts nothing. Each case names one tag so the backend expands
   only that handler, and ONLY keeps the rest of this module out of the
   search. *)
LEMMA SendNone ==
    ASSUME NEW ev, NEW doc, NEW t, ev.tag \in HandleTag
    PROVE  Handle(ev, doc, t).sends = << >>
PROOF
    <1>1. CASE ev.tag = "PromiseGet"
        BY ONLY <1>1, Zenon DEF Handle, HandlePromiseGet, Skip
    <1>2. CASE ev.tag = "PromiseCreate"
        BY ONLY <1>2, Zenon DEF Handle, HandlePromiseCreate, Skip
    <1>3. CASE ev.tag = "PromiseSettle"
        BY ONLY <1>3, Zenon DEF Handle, HandlePromiseSettle, Skip
    <1>4. CASE ev.tag = "PromiseRegisterCallback"
        BY ONLY <1>4, Zenon DEF Handle, HandlePromiseRegisterCallback, Skip
    <1>5. CASE ev.tag = "PromiseRegisterListener"
        BY ONLY <1>5, Zenon DEF Handle, HandlePromiseRegisterListener, Skip
    <1>6. CASE ev.tag = "TaskGet"
        BY ONLY <1>6, Zenon DEF Handle, HandleTaskGet, Skip
    <1>7. CASE ev.tag = "TaskCreate"
        BY ONLY <1>7, Zenon DEF Handle, HandleTaskCreate, Skip
    <1>8. CASE ev.tag = "TaskAcquire"
        BY ONLY <1>8, Zenon DEF Handle, HandleTaskAcquire, Skip
    <1>9. CASE ev.tag = "TaskFence"
        BY ONLY <1>9, Zenon DEF Handle, HandleTaskFence, Skip,
                                HandlePromiseCreate, HandlePromiseSettle
    <1>10. CASE ev.tag = "TaskHeartbeat"
        BY ONLY <1>10, Zenon DEF Handle, HandleTaskHeartbeat, Skip
    <1>11. CASE ev.tag = "TaskSuspend"
        BY ONLY <1>11, Zenon DEF Handle, HandleTaskSuspend, Skip
    <1>12. CASE ev.tag = "TaskFulfill"
        BY ONLY <1>12, Zenon DEF Handle, HandleTaskFulfill, Skip
    <1>13. CASE ev.tag = "TaskRelease"
        BY ONLY <1>13, Zenon DEF Handle, HandleTaskRelease, Skip
    <1>14. CASE ev.tag = "TaskHalt"
        BY ONLY <1>14, Zenon DEF Handle, HandleTaskHalt, Skip
    <1>15. CASE ev.tag = "TaskContinue"
        BY ONLY <1>15, Zenon DEF Handle, HandleTaskContinue, Skip
    <1>16. CASE ev.tag = "Timeout"
        BY ONLY <1>16, Zenon DEF Handle, Skip
    <1>17. ev.tag \in HandleTag
        OBVIOUS
    <1>18. QED
        BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9,
           <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16, <1>17,
           Z3 DEF HandleTag

LEMMA ImageSends ==
    ASSUME NEW st
    PROVE  Image(st).sends
              = Sweep(st.expect, st.at).sends
                  \o Handle(st.ev, Sweep(st.expect, st.at).doc, st.at).sends
PROOF
    <1>1. HIDE DEF Sweep, Handle
    <1>2. Image(st) =
            LET ev    == st.ev
                t     == st.at
                exp   == st.expect
                swept == Sweep(exp, t)
                out   == Handle(ev, swept.doc, t)
            IN  [doc |-> out.doc, sends |-> swept.sends \o out.sends]
        BY ONLY DEF Image
    <1>3. QED
        BY ONLY <1>2, Isa

LEMMA HeadSends ==
    ASSUME NEW seq, NEW docb, NEW sent,
           seq \in Seq(Range(seq)),
           seq # << >>,
           Docs(seq, docb, sent),
           Head(seq).tag = "PutDocument"
    PROVE  Head(seq).sends = sent
PROOF
    <1>1. Head(seq) = seq[1] /\ 1 \in DOMAIN seq
        BY HeadAt, Z3
    <1>2. seq[1].tag = "PutDocument"
        BY <1>1, Z3
    <1>3. seq[1].sends = sent
        BY <1>1, <1>2, Z3 DEF Docs
    <1>4. QED
        BY <1>1, <1>3, Z3

(* The queued sends are the sweep's, followed by the empty handler
   sequence. Delivery posts that sequence, and the clock stays. *)
LEMMA PutOut ==
    ASSUME Queued,
           NEW r \in DOMAIN steps,
           PerformPut(r),
           steps[r].ev.tag \in HandleTag
    PROVE  LET e   == Head(steps[r].pending)
                t   == steps[r].at
                doc == steps[r].expect
            IN  /\ e.sends = Sweep(doc, t).sends \o << >>
                /\ outbox' = Deliver(outbox, e.sends)
                /\ now' = now
                /\ t \in 0 .. now
                /\ t \in Nat
                /\ t /= NoTime
PROOF
    <1> DEFINE e == Head(steps[r].pending)
    <1> DEFINE t == steps[r].at
    <1> DEFINE doc == steps[r].expect
    <1> DEFINE o == OriginOf(steps[r].ev)
    <1>1. now \in Nat
        BY Z3 DEF Queued
    <1>2. steps[r].phase = "perform"
        BY Z3 DEF PerformPut
    <1>3. Match(steps[r], now)
        BY <1>2, Z3 DEF Queued
    <1>4. t \in 0 .. now
        BY <1>3, Z3 DEF Match, t
    <1>5. t \in Nat /\ t /= NoTime
        BY <1>1, <1>4, AtNat, Z3
    <1>6. steps[r].pending \in Seq(Range(steps[r].pending))
          /\ Docs(steps[r].pending,
                  Image(steps[r]).doc, Image(steps[r]).sends)
        BY <1>3, Z3 DEF Match
    <1>7. steps[r].pending # << >> /\ e.tag = "PutDocument" /\ now' = now
        BY PutWrite, Z3 DEF e, o, PerformPut
    <1>8. e.sends = Image(steps[r]).sends
        BY <1>6, <1>7, HeadSends, Z3 DEF e
    <1>9. Image(steps[r]).sends
            = Sweep(steps[r].expect, steps[r].at).sends
                \o Handle(steps[r].ev,
                          Sweep(steps[r].expect, steps[r].at).doc,
                          steps[r].at).sends
        BY ONLY ImageSends, Isa
    <1>9b. Image(steps[r]).sends
            = Sweep(doc, t).sends
                \o Handle(steps[r].ev, Sweep(doc, t).doc, t).sends
        BY ONLY <1>9, Z3 DEF doc, t
    <1>10. Handle(steps[r].ev, Sweep(doc, t).doc, t).sends = << >>
        BY SendNone, Z3
    <1>11. e.sends = Sweep(doc, t).sends \o << >>
        BY <1>8, <1>9b, <1>10, Z3
    <1>12. outbox' = Deliver(outbox, e.sends)
        BY Z3 DEF PerformPut, e
    <1>13. QED
        BY <1>4, <1>5, <1>7, <1>11, <1>12, Z3 DEF e, t, doc

=============================================================================
