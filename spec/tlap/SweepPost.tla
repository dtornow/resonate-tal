----------------------------- MODULE SweepPost -----------------------------
(* Listener sends and retry sends are sequences. Distinct keys let delivery
   post the union, which is what a sweep writes into the outbox. *)
EXTENDS SendSet, PassTag

LEMMA SweepPosted ==
    ASSUME NEW b, NEW doc, NEW t,
           NEW P, NEW S, NEW heard, NEW retried,
           IsFiniteSet(P),
           IsFiniteSet(S),
           heard = SweepListeners(SweepTimeoutAt(doc, t).doc, t).sends,
           retried
             = SweepRetryAt(SweepExpiresAt(
                   SweepCallbacks(
                       SweepListeners(SweepTimeoutAt(doc, t).doc, t).doc, t).doc,
                   t).doc, t).sends,
           P = { x \in [id : { i \in DOMAIN SweepTimeoutAt(doc, t).doc :
                                 SweepTimeoutAt(doc, t).doc[i].promise.state
                                   /= "pending" },
                        address : Address] :
                   x.address
                     \in SweepTimeoutAt(doc, t).doc[x.id].promise.listeners },
           S = { i \in DOMAIN SweepExpiresAt(
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
    PROVE  Deliver(b, Sweep(doc, t).sends)
              = Posted(b, Range(heard) \cup Range(retried))
PROOF
    <1> DEFINE tdoc == SweepTimeoutAt(doc, t).doc
    <1> DEFINE edoc ==
            SweepExpiresAt(
                SweepCallbacks(SweepListeners(tdoc, t).doc, t).doc, t).doc
    <1>1. P = { x \in [id : { i \in DOMAIN tdoc :
                                tdoc[i].promise.state /= "pending" },
                       address : Address] :
                  x.address \in tdoc[x.id].promise.listeners }
        BY DEF tdoc
    <1>2. S = { i \in DOMAIN edoc :
                  edoc[i].task.state = "pending"
                  /\ edoc[i].task.retryTimeoutAt <= t }
        BY DEF tdoc, edoc
    <1>3. \E E : SweepListeners(tdoc, t).sends \in Seq(E)
        BY <1>1, ListenSomeSeq
    <1>4. heard = SweepListeners(tdoc, t).sends
        BY DEF tdoc
    <1>5. \E E : heard \in Seq(E)
        BY <1>3, <1>4
    <1>6. PICK E1 : heard \in Seq(E1)
        BY <1>5
    <1>7. \E E : SweepRetryAt(edoc, t).sends \in Seq(E)
        BY <1>2, RetrySomeSeq
    <1>8. retried = SweepRetryAt(edoc, t).sends
        BY DEF edoc
    <1>9. \E E : retried \in Seq(E)
        BY <1>7, <1>8
    <1>10. PICK E2 : retried \in Seq(E2)
        BY <1>9
    <1> DEFINE Both == E1 \cup E2
    <1>11. E1 \subseteq Both /\ E2 \subseteq Both
        BY DEF Both
    <1>12. heard \in Seq(Both) /\ retried \in Seq(Both)
        BY <1>6, <1>10, <1>11, SeqMonotonic
    <1>13. \A n \in 1 .. Len(SweepListeners(tdoc, t).sends) :
              SweepListeners(tdoc, t).sends[n].message.tag = "Unblock"
        BY <1>1, ListenTags
    <1>14. \A n \in 1 .. Len(heard) : heard[n].message.tag = "Unblock"
        BY <1>4, <1>13
    <1>15. \A n \in 1 .. Len(SweepRetryAt(edoc, t).sends) :
              SweepRetryAt(edoc, t).sends[n].message.tag = "Execute"
        BY <1>2, RetryTags
    <1>16. \A n \in 1 .. Len(retried) : retried[n].message.tag = "Execute"
        BY <1>8, <1>15
    <1>17. \A i, j \in 1 .. Len(SweepListeners(tdoc, t).sends) :
              i /= j =>
                MsgKey(SweepListeners(tdoc, t).sends[i])
                  /= MsgKey(SweepListeners(tdoc, t).sends[j])
        BY <1>1, ListenDistinct
    <1>18. \A i, j \in 1 .. Len(heard) :
              i /= j => MsgKey(heard[i]) /= MsgKey(heard[j])
        BY <1>4, <1>17
    <1>19. \A i, j \in 1 .. Len(SweepRetryAt(edoc, t).sends) :
              i /= j =>
                MsgKey(SweepRetryAt(edoc, t).sends[i])
                  /= MsgKey(SweepRetryAt(edoc, t).sends[j])
        BY <1>2, RetryDistinct
    <1>20. \A i, j \in 1 .. Len(retried) :
              i /= j => MsgKey(retried[i]) /= MsgKey(retried[j])
        BY <1>8, <1>19
    <1>21. QED
        BY <1>4, <1>8, <1>12, <1>14, <1>16, <1>18, <1>20, SweepDeliver

=============================================================================
