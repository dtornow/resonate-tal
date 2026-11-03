------------------------------ MODULE DueBox ------------------------------
(* After the timeout pass, listener pairs are the abstract due set. The
   sweep therefore posts that set, and then the concrete retry ids. *)
EXTENDS Slice, SweepPost

TDoc(doc, t) == SweepTimeoutAt(doc, t).doc

EDoc(doc, t) ==
    SweepExpiresAt(
        SweepCallbacks(SweepListeners(TDoc(doc, t), t).doc, t).doc, t).doc

RetryIds(doc, t) ==
    { i \in DOMAIN EDoc(doc, t) :
        EDoc(doc, t)[i].task.state = "pending"
        /\ EDoc(doc, t)[i].task.retryTimeoutAt <= t }

LEMMA SweepDueBox ==
    ASSUME NEW b, NEW doc, NEW t, DOMAIN doc \subseteq Id
    PROVE  Deliver(b, Sweep(doc, t).sends)
              = BoxAt(BoxN(b, TDoc(doc, t), DueN(TDoc(doc, t), t), t),
                      EDoc(doc, t), RetryIds(doc, t))
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
        BY DEF tdoc, edoc, S
    <1>5. IsFiniteSet(S)
        BY <1>4, RetryDueFinite
    <1>6. Deliver(b, Sweep(doc, t).sends)
            = BoxAt(BoxN(b, SweepTimeoutAt(doc, t).doc, P, t),
                    SweepExpiresAt(
                        SweepCallbacks(
                            SweepListeners(
                                SweepTimeoutAt(doc, t).doc, t).doc, t).doc,
                        t).doc,
                    S)
        BY <1>2, <1>3, <1>4, <1>5, SweepBox
    <1>7. QED
        BY <1>6 DEF tdoc, edoc, P, S, TDoc, EDoc, RetryIds

=============================================================================
