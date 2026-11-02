----------------------------- MODULE SweepPost -----------------------------
(* Listener sends and retry sends are sequences. Distinct keys let delivery
   post the union, which is what a sweep writes into the outbox. *)
EXTENDS SendSet, PassTag

(* A retry id is an element of the document, so a document whose domain
   sits in Id has finitely many due retries. *)
LEMMA RetryFinite ==
    ASSUME NEW doc, NEW t, DOMAIN doc \subseteq Id
    PROVE  IsFiniteSet({ i \in DOMAIN doc :
                           doc[i].task.state = "pending"
                           /\ doc[i].task.retryTimeoutAt <= t })
PROOF
    <1> DEFINE S ==
            { i \in DOMAIN doc :
                doc[i].task.state = "pending"
                /\ doc[i].task.retryTimeoutAt <= t }
    <1>1. S \subseteq DOMAIN doc
        BY DEF S
    <1>2. S \subseteq Id
        BY <1>1
    <1>3. IsFiniteSet(Id)
        BY FiniteOrigin, FiniteRest, IdFinite
    <1>4. QED
        BY <1>2, <1>3, FS_Subset DEF S

(* A listener pair is an id from that same domain together with an address. *)
LEMMA ListenFinite ==
    ASSUME NEW doc, DOMAIN doc \subseteq Id
    PROVE  IsFiniteSet(
              { x \in [id : { i \in DOMAIN doc :
                                 doc[i].promise.state /= "pending" },
                       address : Address] :
                   x.address \in doc[x.id].promise.listeners })
PROOF
    <1> DEFINE P ==
            { x \in [id : { i \in DOMAIN doc :
                               doc[i].promise.state /= "pending" },
                     address : Address] :
                 x.address \in doc[x.id].promise.listeners }
    <1> DEFINE Op(p) == [id |-> p[1], address |-> p[2]]
    <1> DEFINE Img == { Op(p) : p \in Id \X Address }
    <1>1. IsFiniteSet(Id) /\ IsFiniteSet(Address)
        BY FiniteOrigin, FiniteRest, FiniteAddress, IdFinite
    <1>2. IsFiniteSet(Id \X Address)
        BY <1>1, FS_Product
    <1>3. LET T == { Op(x) : x \in Id \X Address }
          IN  IsFiniteSet(T)
        BY <1>2, FS_Image
    <1>4. IsFiniteSet(Img)
        BY <1>3 DEF Img
    <1>5. P \subseteq Img
        <2> SUFFICES ASSUME NEW x \in P
                     PROVE  x \in Img
            OBVIOUS
        <2>1. x \in [id : { i \in DOMAIN doc :
                               doc[i].promise.state /= "pending" },
                     address : Address]
            BY DEF P
        <2>2. x.id \in DOMAIN doc /\ x.address \in Address
            BY <2>1, Z3
        <2>3. x.id \in Id
            BY <2>2
        <2> DEFINE p == <<x.id, x.address>>
        <2>4. p \in Id \X Address
            BY <2>2, <2>3, PairIn DEF p
        <2>5. x = [id |-> x.id, address |-> x.address]
            BY <2>1, Isa
        <2>6. x = Op(p)
            BY <2>5 DEF Op, p
        <2>7. QED
            BY <2>4, <2>6 DEF Img
    <1>6. QED
        BY <1>4, <1>5, FS_Subset DEF P

(* The timeout pass rewrites records in place, so the domain is unchanged.
   Later passes can inherit finiteness from the document they start on. *)
LEMMA TimeoutDom ==
    ASSUME NEW doc, NEW t
    PROVE  DOMAIN SweepTimeoutAt(doc, t).doc = DOMAIN doc
PROOF
    <1> DEFINE due ==
            { i \in DOMAIN doc :
                doc[i].promise.state = "pending"
                /\ doc[i].promise.timeoutAt <= t }
    <1> DEFINE sw == SweepTimeoutAt(doc, t).doc
    <1>1. CASE due = {}
        <2>1. sw = doc
            BY <1>1 DEF due, sw, SweepTimeoutAt
        <2>2. QED
            BY <2>1
    <1>2. CASE due # {}
        <2>1. sw = [ i \in DOMAIN doc |->
                       IF i \in due THEN Project(doc[i], t) ELSE doc[i] ]
            BY <1>2 DEF due, sw, SweepTimeoutAt
        <2>2. DOMAIN [ i \in DOMAIN doc |->
                         IF i \in due THEN Project(doc[i], t) ELSE doc[i] ]
                = DOMAIN doc
            BY DomCtor
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2

(* The listener set of a timeout pass is finite when the store started finite. *)
LEMMA ListenDueFinite ==
    ASSUME NEW doc, NEW t, NEW P, DOMAIN doc \subseteq Id,
           P = { x \in [id : { i \in DOMAIN SweepTimeoutAt(doc, t).doc :
                                 SweepTimeoutAt(doc, t).doc[i].promise.state
                                   /= "pending" },
                        address : Address] :
                   x.address
                     \in SweepTimeoutAt(doc, t).doc[x.id].promise.listeners }
    PROVE  IsFiniteSet(P)
PROOF
    <1> DEFINE tdoc == SweepTimeoutAt(doc, t).doc
    <1>1. DOMAIN tdoc = DOMAIN doc
        BY TimeoutDom DEF tdoc
    <1>2. DOMAIN tdoc \subseteq Id
        BY <1>1
    <1>3. IsFiniteSet(
              { x \in [id : { i \in DOMAIN tdoc :
                                 tdoc[i].promise.state /= "pending" },
                       address : Address] :
                   x.address \in tdoc[x.id].promise.listeners })
        BY <1>2, ListenFinite
    <1>4. P = { x \in [id : { i \in DOMAIN tdoc :
                                 tdoc[i].promise.state /= "pending" },
                       address : Address] :
                  x.address \in tdoc[x.id].promise.listeners }
        BY DEF tdoc
    <1>5. QED
        BY <1>3, <1>4

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
