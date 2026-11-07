----------------------------- MODULE SweepPost -----------------------------
(* Listener sends and retry sends are sequences. Distinct keys let delivery
   post the union. Delivery of the concatenation is the listener box, then
   the retry box. *)
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

(* Each later pass rewrites records in place. The retry set is read from
   the document those passes leave, so its domain is the one we started with. *)
LEMMA ListenDom ==
    ASSUME NEW doc, NEW t
    PROVE  DOMAIN SweepListeners(doc, t).doc = DOMAIN doc
PROOF
    <1> DEFINE due ==
            { x \in [id : { i \in DOMAIN doc :
                               doc[i].promise.state /= "pending" },
                     address : Address] :
                 x.address \in doc[x.id].promise.listeners }
    <1> DEFINE sw == SweepListeners(doc, t).doc
    <1>1. CASE due = {}
        <2>1. sw = doc
            BY <1>1 DEF due, sw, SweepListeners
        <2>2. QED
            BY <2>1
    <1>2. CASE due # {}
        <2>1. sw = [ i \in DOMAIN doc |->
                       IF doc[i].promise.state /= "pending"
                          /\ doc[i].promise.listeners /= {} THEN
                            DropListeners(doc[i])
                       ELSE
                            doc[i] ]
            BY <1>2 DEF due, sw, SweepListeners
        <2>2. DOMAIN [ i \in DOMAIN doc |->
                         IF doc[i].promise.state /= "pending"
                            /\ doc[i].promise.listeners /= {} THEN
                              DropListeners(doc[i])
                         ELSE
                              doc[i] ]
                = DOMAIN doc
            BY DomCtor
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2

LEMMA CallDom ==
    ASSUME NEW doc, NEW t
    PROVE  DOMAIN SweepCallbacks(doc, t).doc = DOMAIN doc
PROOF
    <1> DEFINE due ==
            { x \in [id : { i \in DOMAIN doc :
                               doc[i].promise.state /= "pending" },
                     awaiter : Id] :
                 x.awaiter \in doc[x.id].promise.callbacks }
    <1> DEFINE resumes(w) == { x.id : x \in { y \in due : y.awaiter = w } }
    <1> DEFINE woken == { x.awaiter : x \in due } \cap DOMAIN doc
    <1> DEFINE sw == SweepCallbacks(doc, t).doc
    <1> DEFINE body(i) ==
            LET struck == IF doc[i].promise.state /= "pending"
                             /\ doc[i].promise.callbacks /= {} THEN
                              DropCallbacks(doc[i])
                          ELSE
                              doc[i]
            IN  IF i \notin woken \/ struck.task.state \in {"none", "fulfilled"} THEN
                    struck
                ELSE IF struck.task.state = "suspended" THEN
                    Wake(struck, resumes(i), t)
                ELSE
                    AddResumes(struck, resumes(i))
    <1>1. CASE due = {}
        <2>1. sw = doc
            BY <1>1 DEF due, sw, SweepCallbacks
        <2>2. QED
            BY <2>1
    <1>2. CASE due # {}
        <2>1. sw = [ i \in DOMAIN doc |-> body(i) ]
            BY <1>2 DEF due, resumes, woken, sw, body, SweepCallbacks
        <2>2. DOMAIN [ i \in DOMAIN doc |-> body(i) ] = DOMAIN doc
            BY DomCtor
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2

LEMMA ExpireDom ==
    ASSUME NEW doc, NEW t
    PROVE  DOMAIN SweepExpiresAt(doc, t).doc = DOMAIN doc
PROOF
    <1> DEFINE due ==
            { i \in DOMAIN doc :
                doc[i].task.state = "acquired"
                /\ doc[i].task.leaseTimeoutAt <= t }
    <1> DEFINE sw == SweepExpiresAt(doc, t).doc
    <1>1. CASE due = {}
        <2>1. sw = doc
            BY <1>1 DEF due, sw, SweepExpiresAt
        <2>2. QED
            BY <2>1
    <1>2. CASE due # {}
        <2>1. sw = [ i \in DOMAIN doc |->
                       IF i \in due THEN
                           [ doc[i] EXCEPT !.task.state          = "pending",
                                           !.task.pid            = NoPid,
                                           !.task.ttl            = NoTime,
                                           !.task.leaseTimeoutAt = NoTime,
                                           !.task.retryTimeoutAt = t ]
                       ELSE
                           doc[i] ]
            BY <1>2 DEF due, sw, SweepExpiresAt
        <2>2. DOMAIN [ i \in DOMAIN doc |->
                         IF i \in due THEN
                             [ doc[i] EXCEPT !.task.state          = "pending",
                                             !.task.pid            = NoPid,
                                             !.task.ttl            = NoTime,
                                             !.task.leaseTimeoutAt = NoTime,
                                             !.task.retryTimeoutAt = t ]
                         ELSE
                             doc[i] ]
                = DOMAIN doc
            BY DomCtor
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2

LEMMA RetryDueFinite ==
    ASSUME NEW doc, NEW t, NEW S, DOMAIN doc \subseteq Id,
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
    PROVE  IsFiniteSet(S)
PROOF
    <1> DEFINE tdoc == SweepTimeoutAt(doc, t).doc
    <1> DEFINE ldoc == SweepListeners(tdoc, t).doc
    <1> DEFINE cdoc == SweepCallbacks(ldoc, t).doc
    <1> DEFINE edoc == SweepExpiresAt(cdoc, t).doc
    <1>1. DOMAIN tdoc = DOMAIN doc
        BY TimeoutDom DEF tdoc
    <1>2. DOMAIN ldoc = DOMAIN tdoc
        BY ListenDom DEF ldoc
    <1>3. DOMAIN cdoc = DOMAIN ldoc
        BY CallDom DEF cdoc
    <1>4. DOMAIN edoc = DOMAIN cdoc
        BY ExpireDom DEF edoc
    <1>5. DOMAIN edoc = DOMAIN doc
        BY <1>1, <1>2, <1>3, <1>4
    <1>6. DOMAIN edoc \subseteq Id
        BY <1>5
    <1>7. IsFiniteSet({ i \in DOMAIN edoc :
                          edoc[i].task.state = "pending"
                          /\ edoc[i].task.retryTimeoutAt <= t })
        BY <1>6, RetryFinite
    <1>8. S = { i \in DOMAIN edoc :
                  edoc[i].task.state = "pending"
                  /\ edoc[i].task.retryTimeoutAt <= t }
        BY DEF tdoc, ldoc, cdoc, edoc
    <1>9. QED
        BY <1>7, <1>8

(* SetToSeq lays the due ids out. Delivery of that list is the abstract retry post. *)
LEMMA RetryPosted ==
    ASSUME NEW doc, NEW t, NEW b, NEW S,
           IsFiniteSet(S),
           S = { i \in DOMAIN doc :
                   doc[i].task.state = "pending"
                   /\ doc[i].task.retryTimeoutAt <= t }
    PROVE  Deliver(b, SweepRetryAt(doc, t).sends) = BoxAt(b, doc, S)
PROOF
    <1> DEFINE q == SetToSeq(S)
    <1>1. /\ q \in Seq(S)
          /\ IsInjective(q)
          /\ Range(q) = S
        BY SetToSeqAny DEF q
    <1>2. S \subseteq DOMAIN doc
        BY Zenon
    <1>3. QED
        BY <1>1, <1>2, RetrySend DEF q

(* A listener pair names a promise that is no longer pending, so projection
   leaves the record alone and the Unblock carries that state. *)
LEMMA ListenMatch ==
    ASSUME NEW doc, NEW t, NEW P,
           P = { x \in [id : { i \in DOMAIN doc :
                                 doc[i].promise.state /= "pending" },
                        address : Address] :
                   x.address \in doc[x.id].promise.listeners }
    PROVE  \A p \in P :
              UnblockMsg(doc, p.id, p.address, t).message.state
                = doc[p.id].promise.state
PROOF
    <1>1. ASSUME NEW p \in P
          PROVE  UnblockMsg(doc, p.id, p.address, t).message.state
                    = doc[p.id].promise.state
        <2> DEFINE obj == doc[p.id]
        <2>1. obj.promise.state /= "pending"
            BY <1>1 DEF obj
        <2>2. QED
            BY <2>1, ProjectId DEF UnblockMsg, obj
    <1>2. QED
        BY <1>1

LEMMA ListenPosted ==
    ASSUME NEW doc, NEW t, NEW b, NEW P,
           IsFiniteSet(P),
           P = { x \in [id : { i \in DOMAIN doc :
                                 doc[i].promise.state /= "pending" },
                        address : Address] :
                   x.address \in doc[x.id].promise.listeners }
    PROVE  Deliver(b, SweepListeners(doc, t).sends) = BoxN(b, doc, P, t)
PROOF
    <1> DEFINE q == SetToSeq(P)
    <1>1. /\ q \in Seq(P)
          /\ IsInjective(q)
          /\ Range(q) = P
        BY SetToSeqAny DEF q
    <1>2. \A p \in P :
             UnblockMsg(doc, p.id, p.address, t).message.state
               = doc[p.id].promise.state
        BY ListenMatch
    <1>3. QED
        BY <1>1, <1>2, ListenSend DEF q

(* The outbox fold is a left fold, so a concatenated send list is the
   second list applied to the box the first list produced. *)
LEMMA DeliverSplit ==
    ASSUME NEW b, NEW E,
           NEW s1 \in Seq(E), NEW s2 \in Seq(E)
    PROVE  Deliver(b, s1 \o s2) = Deliver(Deliver(b, s1), s2)
PROOF
    <1> DEFINE Ok(seq) ==
            seq \in Seq(E) =>
              Deliver(b, s1 \o seq) = Deliver(Deliver(b, s1), seq)
    <1>1. Ok(<< >>)
        <2>1. << >> \in Seq(E)
            BY EmptySeq
        <2>2. s1 \o << >> = s1
            BY ConcatEmptySeq
        <2>3. Deliver(Deliver(b, s1), << >>) = Deliver(b, s1)
            BY DeliverNil
        <2>4. QED
            BY <2>1, <2>2, <2>3, Zenon DEF Ok
    <1>2. ASSUME NEW s \in Seq(E), NEW e \in E, Ok(s)
          PROVE  Ok(Append(s, e))
        <2> DEFINE src == Append(s, e)
        <2> DEFINE cat == s1 \o s
        <2> DEFINE left == Append(cat, e)
        <2> DEFINE right == s1 \o src
        <2>1. /\ src \in Seq(E)
              /\ Len(src) = Len(s) + 1
              /\ \A i \in 1 .. Len(s) : src[i] = s[i]
              /\ src[Len(s) + 1] = e
            BY AppendProperties DEF src
        <2>2. /\ cat \in Seq(E)
              /\ Len(cat) = Len(s1) + Len(s)
              /\ \A i \in 1 .. (Len(s1) + Len(s)) :
                    cat[i] = IF i <= Len(s1) THEN s1[i]
                             ELSE s[i - Len(s1)]
            BY ConcatProperties DEF cat
        <2>3. /\ left \in Seq(E)
              /\ Len(left) = Len(cat) + 1
              /\ \A i \in 1 .. Len(cat) : left[i] = cat[i]
              /\ left[Len(cat) + 1] = e
            BY <2>2, AppendProperties DEF left
        <2>4. /\ right \in Seq(E)
              /\ Len(right) = Len(s1) + Len(src)
              /\ \A i \in 1 .. (Len(s1) + Len(src)) :
                    right[i] = IF i <= Len(s1) THEN s1[i]
                               ELSE src[i - Len(s1)]
            BY <2>1, ConcatProperties DEF right
        <2>5. Len(s1) \in Nat /\ Len(s) \in Nat
            BY LenProperties
        <2>6. /\ Len(left) = Len(s1) + Len(s) + 1
              /\ Len(right) = Len(s1) + Len(s) + 1
            BY <2>1, <2>2, <2>3, <2>4, <2>5, Z3
        <2>7. Len(left) = Len(right)
            BY <2>6
        <2>8. \A i \in 1 .. Len(left) : left[i] = right[i]
            <3>1. ASSUME NEW i \in 1 .. Len(left)
                  PROVE  left[i] = right[i]
                <4> DEFINE n1 == Len(s1)
                <4> DEFINE n2 == Len(s)
                <4>1. i \in 1 .. (n1 + n2 + 1)
                    BY <2>6, <3>1 DEF n1, n2
                <4>2. CASE i <= n1
                    BY <2>2, <2>3, <2>4, <2>6, <4>1, <4>2, Z3 DEF n1, n2
                <4>3. CASE i > n1 /\ i <= n1 + n2
                    <5>1. i - n1 \in 1 .. n2
                        BY <2>5, <4>1, <4>3, Z3 DEF n1, n2
                    <5>2. QED
                        BY <2>1, <2>2, <2>3, <2>4, <2>6, <4>3, <5>1, Z3
                           DEF n1, n2
                <4>4. CASE i = n1 + n2 + 1
                    BY <2>1, <2>2, <2>3, <2>4, <2>6, <4>4, Z3 DEF n1, n2
                <4>5. QED
                    BY <2>5, <4>1, <4>2, <4>3, <4>4, Z3 DEF n1, n2
            <3>2. QED
                BY <3>1
        <2>9. left = right
            BY <2>3, <2>4, <2>7, <2>8, SeqEqual
        <2>10. Deliver(b, left) = Post(Deliver(b, cat), e)
            BY <2>2, DeliverAppend DEF left
        <2>11. Deliver(Deliver(b, s1), src)
                  = Post(Deliver(Deliver(b, s1), s), e)
            BY DeliverAppend DEF src
        <2>12. Deliver(b, s1 \o s) = Deliver(Deliver(b, s1), s)
            BY <1>2 DEF Ok
        <2>12a. Deliver(b, cat) = Deliver(Deliver(b, s1), s)
            BY <2>12 DEF cat
        <2>13. Post(Deliver(b, cat), e)
                  = Post(Deliver(Deliver(b, s1), s), e)
            BY <2>12a
        <2>14. Deliver(b, right) = Deliver(Deliver(b, s1), src)
            BY <2>9, <2>10, <2>11, <2>13
        <2>15. QED
            BY <2>1, <2>14 DEF Ok, src, right
    <1>3. \A s \in Seq(E), e \in E : Ok(s) => Ok(Append(s, e))
        BY <1>2
    <1> DEFINE L(k) ==
            \A seq \in Seq(E) : Len(seq) = k => Ok(seq)
    <1>4. \A seq \in Seq(E) : Len(seq) = 0 => seq = << >>
        BY EmptySeq, Zenon
    <1>5. L(0)
        BY <1>1, <1>4, Zenon DEF L
    <1>6. ASSUME NEW n \in Nat
          PROVE  L(n) => L(n + 1)
        <2> HIDE DEF Ok
        <2>1. QED
            BY <1>3, StepR DEF L
    <1>7. \A n \in Nat : L(n) => L(n + 1)
        BY <1>6
    <1>8. \A n \in Nat : L(n)
        BY <1>5, <1>7, NatInduction DEF L
    <1>9. Len(s2) \in Nat
        BY LenProperties
    <1>10. L(Len(s2))
        BY <1>8, <1>9, Zenon DEF L
    <1>11. Ok(s2)
        BY <1>10 DEF L
    <1>12. QED
        BY <1>11 DEF Ok

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

(* Listeners post first and retries post onto that box, which is what
   delivering the concatenated sweep sends does. *)
LEMMA SweepBox ==
    ASSUME NEW b, NEW doc, NEW t,
           NEW P, NEW S,
           IsFiniteSet(P),
           IsFiniteSet(S),
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
              = BoxAt(BoxN(b, SweepTimeoutAt(doc, t).doc, P, t),
                      SweepExpiresAt(
                          SweepCallbacks(
                              SweepListeners(
                                  SweepTimeoutAt(doc, t).doc, t).doc, t).doc,
                          t).doc,
                      S)
PROOF
    <1> DEFINE tdoc == SweepTimeoutAt(doc, t).doc
    <1> DEFINE edoc ==
            SweepExpiresAt(
                SweepCallbacks(SweepListeners(tdoc, t).doc, t).doc, t).doc
    <1> DEFINE lis == SweepListeners(tdoc, t).sends
    <1> DEFINE ry == SweepRetryAt(edoc, t).sends
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
    <1>4. lis = SweepListeners(tdoc, t).sends
        BY DEF tdoc, lis
    <1>5. \E E : lis \in Seq(E)
        BY <1>3, <1>4
    <1>6. PICK E1 : lis \in Seq(E1)
        BY <1>5
    <1>7. \E E : SweepRetryAt(edoc, t).sends \in Seq(E)
        BY <1>2, RetrySomeSeq
    <1>8. ry = SweepRetryAt(edoc, t).sends
        BY DEF edoc, ry
    <1>9. \E E : ry \in Seq(E)
        BY <1>7, <1>8
    <1>10. PICK E2 : ry \in Seq(E2)
        BY <1>9
    <1> DEFINE Both == E1 \cup E2
    <1>11. E1 \subseteq Both /\ E2 \subseteq Both
        BY DEF Both
    <1>12. lis \in Seq(Both) /\ ry \in Seq(Both)
        BY <1>6, <1>10, <1>11, SeqMonotonic
    <1>13. lis = SweepListeners(SweepTimeoutAt(doc, t).doc, t).sends
        BY DEF tdoc, lis
    <1>14. ry = SweepRetryAt(SweepExpiresAt(
                    SweepCallbacks(
                        SweepListeners(
                            SweepTimeoutAt(doc, t).doc, t).doc, t).doc,
                    t).doc, t).sends
        BY DEF tdoc, edoc, ry
    <1>15. Sweep(doc, t).sends = lis \o ry
        BY <1>12, <1>13, <1>14, SweepSends
    <1>16. Deliver(b, lis \o ry) = Deliver(Deliver(b, lis), ry)
        BY <1>12, DeliverSplit
    <1>17. Deliver(b, SweepListeners(tdoc, t).sends) = BoxN(b, tdoc, P, t)
        BY <1>1, ListenPosted
    <1>18. Deliver(b, lis) = BoxN(b, tdoc, P, t)
        BY <1>4, <1>17
    <1>19. Deliver(BoxN(b, tdoc, P, t), SweepRetryAt(edoc, t).sends)
              = BoxAt(BoxN(b, tdoc, P, t), edoc, S)
        BY <1>2, RetryPosted
    <1>20. Deliver(BoxN(b, tdoc, P, t), ry)
              = BoxAt(BoxN(b, tdoc, P, t), edoc, S)
        BY <1>8, <1>19
    <1>21. Deliver(b, lis \o ry)
              = BoxAt(BoxN(b, tdoc, P, t), edoc, S)
        BY <1>16, <1>18, <1>20
    <1>22. BoxAt(BoxN(b, tdoc, P, t), edoc, S)
              = BoxAt(BoxN(b, SweepTimeoutAt(doc, t).doc, P, t),
                      SweepExpiresAt(
                          SweepCallbacks(
                              SweepListeners(
                                  SweepTimeoutAt(doc, t).doc, t).doc, t).doc,
                          t).doc,
                      S)
        BY DEF tdoc, edoc
    <1>23. QED
        BY <1>15, <1>21, <1>22

=============================================================================
