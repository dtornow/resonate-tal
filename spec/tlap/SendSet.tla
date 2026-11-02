----------------------------- MODULE SendSet -----------------------------
(* A sweep pass lists one message per due element. Delivery posts that set,
   whatever order SetToSeq picked. The enumeration facts are assumptions
   here; ToSeq proves them, and instantiating ToSeq from this module
   crashes TLAPS 1.5.0. *)
EXTENDS Listen, Outbox

LEMMA RetryImg ==
    ASSUME NEW doc, NEW S, NEW q \in Seq(S), Range(q) = S
    PROVE  { RetryMsg(doc, q[n]) : n \in 1 .. Len(q) }
              = { RetryMsg(doc, x) : x \in S }
PROOF
    <1>1. DOMAIN q = 1 .. Len(q) /\ Len(q) \in Nat
        BY LenProperties
    <1>2. ASSUME NEW y
          PROVE  y \in { RetryMsg(doc, q[n]) : n \in 1 .. Len(q) }
                  <=> y \in { RetryMsg(doc, x) : x \in S }
        <2>1. ASSUME NEW n \in 1 .. Len(q), y = RetryMsg(doc, q[n])
              PROVE  y \in { RetryMsg(doc, x) : x \in S }
            <3>1. q[n] \in Range(q)
                BY <1>1, <2>1 DEF Range
            <3>2. q[n] \in S
                BY <3>1
            <3>3. QED
                BY <2>1, <3>2
        <2>2. ASSUME NEW x \in S, y = RetryMsg(doc, x)
              PROVE  y \in { RetryMsg(doc, q[n]) : n \in 1 .. Len(q) }
            <3>1. x \in Range(q)
                OBVIOUS
            <3>2. \E n \in 1 .. Len(q) : q[n] = x
                BY <1>1, <3>1 DEF Range
            <3>3. QED
                BY <2>2, <3>2
        <2>3. QED
            BY <2>1, <2>2, Zenon
    <1>3. QED
        BY <1>2, SetExtensionality

LEMMA RetryKeys ==
    ASSUME NEW doc, NEW S, NEW q \in Seq(S), IsInjective(q),
           S \subseteq DOMAIN doc, Range(q) \subseteq S
    PROVE  \A i, j \in 1 .. Len(q) :
              i /= j => MsgKey(RetryMsg(doc, q[i])) /= MsgKey(RetryMsg(doc, q[j]))
PROOF
    <1>1. DOMAIN q = 1 .. Len(q)
        BY LenProperties
    <1>2. ASSUME NEW i \in 1 .. Len(q), NEW j \in 1 .. Len(q), i /= j
          PROVE  MsgKey(RetryMsg(doc, q[i])) /= MsgKey(RetryMsg(doc, q[j]))
        <2>1. q[i] /= q[j]
            BY <1>1, <1>2 DEF IsInjective
        <2>2. q[i] \in S /\ q[j] \in S
            BY <1>1, <1>2, LenProperties
        <2>3. q[i] \in DOMAIN doc /\ q[j] \in DOMAIN doc
            BY <2>2
        <2>4. QED
            BY <2>1, <2>3, ExecKey
    <1>3. QED
        BY <1>2

LEMMA RetrySend ==
    ASSUME NEW doc, NEW t, NEW b, NEW S, NEW q,
           q = SetToSeq(S), q \in Seq(S), IsInjective(q), Range(q) = S,
           S \subseteq DOMAIN doc,
           S = { i \in DOMAIN doc :
                   doc[i].task.state = "pending"
                   /\ doc[i].task.retryTimeoutAt <= t }
    PROVE  Deliver(b, SweepRetryAt(doc, t).sends) = BoxAt(b, doc, S)
PROOF
    <1>1. CASE S = {}
        <2>1. SweepRetryAt(doc, t).sends = << >>
            BY <1>1 DEF SweepRetryAt
        <2>2. Deliver(b, << >>) = b
            BY DeliverNil
        <2>3. Msgs(doc, S) = {}
            BY <1>1 DEF Msgs
        <2>4. BoxAt(b, doc, S) = b
            BY <2>3 DEF BoxAt, Posted
        <2>5. QED
            BY <2>1, <2>2, <2>4
    <1>2. CASE S # {}
        <2> DEFINE sends ==
                [ n \in 1 .. Len(q) |-> RetryMsg(doc, q[n]) ]
        <2>1. SweepRetryAt(doc, t).sends = sends
            BY <1>2 DEF SweepRetryAt, RetryMsg, sends
        <2>2. { RetryMsg(doc, q[n]) : n \in 1 .. Len(q) }
                = { RetryMsg(doc, x) : x \in S }
            BY RetryImg
        <2>3. Range(sends) = { RetryMsg(doc, q[n]) : n \in 1 .. Len(q) }
            <3>1. Len(q) \in Nat /\ DOMAIN q = 1 .. Len(q)
                BY LenProperties
            <3>2. DOMAIN sends = 1 .. Len(q)
                BY <3>1 DEF sends
            <3>3. \A n \in 1 .. Len(q) : sends[n] = RetryMsg(doc, q[n])
                BY <3>1 DEF sends
            <3>4. QED
                BY <3>2, <3>3 DEF Range
        <2>4. Range(sends) = Msgs(doc, S)
            BY <2>2, <2>3 DEF Msgs
        <2>5. sends \in Seq(Range(sends))
            <3>1. Len(q) \in Nat
                BY LenProperties
            <3>2. \A n \in 1 .. Len(q) : sends[n] \in Range(sends)
                BY <2>3, <3>1 DEF sends, Range
            <3>3. QED
                BY <3>1, <3>2, IsASeq DEF sends
        <2>6. \A i, j \in 1 .. Len(sends) :
                 i /= j => MsgKey(sends[i]) /= MsgKey(sends[j])
            <3>1. Len(sends) = Len(q)
                BY LenProperties DEF sends
            <3>2. \A n \in 1 .. Len(q) : sends[n] = RetryMsg(doc, q[n])
                BY LenProperties DEF sends
            <3>3. \A i, j \in 1 .. Len(q) :
                     i /= j => MsgKey(RetryMsg(doc, q[i])) /= MsgKey(RetryMsg(doc, q[j]))
                BY RetryKeys
            <3>4. QED
                BY <3>1, <3>2, <3>3
        <2>7. Deliver(b, sends) = Posted(b, Range(sends))
            BY <2>5, <2>6, DeliverPosted
        <2>8. QED
            BY <2>1, <2>4, <2>7 DEF BoxAt
    <1>3. QED
        BY <1>1, <1>2

LEMMA ListenImg ==
    ASSUME NEW doc, NEW t, NEW P, NEW q \in Seq(P), Range(q) = P
    PROVE  { UnblockMsg(doc, q[n].id, q[n].address, t) : n \in 1 .. Len(q) }
              = { UnblockMsg(doc, p.id, p.address, t) : p \in P }
PROOF
    <1>1. DOMAIN q = 1 .. Len(q) /\ Len(q) \in Nat
        BY LenProperties
    <1>2. ASSUME NEW y
          PROVE  y \in { UnblockMsg(doc, q[n].id, q[n].address, t) :
                           n \in 1 .. Len(q) }
                  <=> y \in { UnblockMsg(doc, p.id, p.address, t) : p \in P }
        <2>1. ASSUME NEW n \in 1 .. Len(q),
                     y = UnblockMsg(doc, q[n].id, q[n].address, t)
              PROVE  y \in { UnblockMsg(doc, p.id, p.address, t) : p \in P }
            <3>1. q[n] \in Range(q)
                BY <1>1, <2>1 DEF Range
            <3>2. q[n] \in P
                BY <3>1
            <3>3. QED
                BY <2>1, <3>2
        <2>2. ASSUME NEW p \in P, y = UnblockMsg(doc, p.id, p.address, t)
              PROVE  y \in { UnblockMsg(doc, q[n].id, q[n].address, t) :
                               n \in 1 .. Len(q) }
            <3>1. p \in Range(q)
                OBVIOUS
            <3>2. \E n \in 1 .. Len(q) : q[n] = p
                BY <1>1, <3>1 DEF Range
            <3>3. QED
                BY <2>2, <3>2
        <2>3. QED
            BY <2>1, <2>2, Zenon
    <1>3. QED
        BY <1>2, SetExtensionality

LEMMA ListenKeys ==
    ASSUME NEW doc, NEW t, NEW P, NEW q \in Seq(P), IsInjective(q),
           P \subseteq [id : DOMAIN doc, address : Address]
    PROVE  \A i, j \in 1 .. Len(q) :
              i /= j =>
                MsgKey(UnblockMsg(doc, q[i].id, q[i].address, t))
                  /= MsgKey(UnblockMsg(doc, q[j].id, q[j].address, t))
PROOF
    <1>1. DOMAIN q = 1 .. Len(q)
        BY LenProperties
    <1>2. ASSUME NEW i \in 1 .. Len(q), NEW j \in 1 .. Len(q), i /= j
          PROVE  MsgKey(UnblockMsg(doc, q[i].id, q[i].address, t))
                    /= MsgKey(UnblockMsg(doc, q[j].id, q[j].address, t))
        <2>1. q[i] /= q[j]
            BY <1>1, <1>2 DEF IsInjective
        <2>2. q[i] \in P /\ q[j] \in P
            BY <1>1, <1>2, LenProperties
        <2>3. q[i] \in [id : DOMAIN doc, address : Address]
                /\ q[j] \in [id : DOMAIN doc, address : Address]
            BY <2>2
        <2>4. QED
            BY <2>1, <2>3, UnblockKey
    <1>3. QED
        BY <1>2

LEMMA ListenSend ==
    ASSUME NEW doc, NEW t, NEW b, NEW P, NEW q,
           q = SetToSeq(P), q \in Seq(P), IsInjective(q), Range(q) = P,
           P = { x \in [id : { i \in DOMAIN doc :
                                 doc[i].promise.state /= "pending" },
                        address : Address] :
                   x.address \in doc[x.id].promise.listeners },
           \A p \in P :
              UnblockMsg(doc, p.id, p.address, t).message.state
                = doc[p.id].promise.state
    PROVE  Deliver(b, SweepListeners(doc, t).sends) = BoxN(b, doc, P, t)
PROOF
    <1>1. P \subseteq [id : DOMAIN doc, address : Address]
        BY Zenon
    <1>2. CASE P = {}
        <2>1. SweepListeners(doc, t).sends = << >>
            BY <1>2 DEF SweepListeners
        <2>2. Deliver(b, << >>) = b
            BY DeliverNil
        <2>3. MsgN(doc, P, t) = {}
            BY <1>2 DEF MsgN
        <2>4. BoxN(b, doc, P, t) = b
            BY <2>3 DEF BoxN, Posted
        <2>5. QED
            BY <2>1, <2>2, <2>4
    <1>3. CASE P # {}
        <2> DEFINE sends ==
                [ n \in 1 .. Len(q) |->
                    UnblockMsg(doc, q[n].id, q[n].address, t) ]
        <2>1. \A n \in 1 .. Len(q) :
                 q[n] \in P
            <3>1. ASSUME NEW n \in 1 .. Len(q)
                  PROVE  q[n] \in P
                BY ElementOfSeq
            <3>2. QED
                BY <3>1
        <2>2. ASSUME NEW p \in P
              PROVE  UnblockMsg(doc, p.id, p.address, t)
                       = [ address |-> p.address,
                           message |-> [ tag   |-> "Unblock",
                                         id    |-> p.id,
                                         state |-> doc[p.id].promise.state ] ]
            <3>1. UnblockMsg(doc, p.id, p.address, t).message.state
                    = doc[p.id].promise.state
                BY Zenon
            <3>2. UnblockMsg(doc, p.id, p.address, t)
                    = [ address |-> p.address,
                        message |-> [ tag   |-> "Unblock",
                                      id    |-> p.id,
                                      state |-> UnblockMsg(doc, p.id, p.address, t).message.state ] ]
                BY DEF UnblockMsg
            <3>3. QED
                BY <3>1, <3>2
        <2>3. SweepListeners(doc, t).sends = sends
            BY <1>3, <2>1, <2>2 DEF SweepListeners, sends
        <2>4. { UnblockMsg(doc, q[n].id, q[n].address, t) : n \in 1 .. Len(q) }
                = { UnblockMsg(doc, p.id, p.address, t) : p \in P }
            BY ListenImg
        <2>5. Range(sends)
                = { UnblockMsg(doc, q[n].id, q[n].address, t) :
                      n \in 1 .. Len(q) }
            <3>1. Len(q) \in Nat /\ DOMAIN q = 1 .. Len(q)
                BY LenProperties
            <3>2. DOMAIN sends = 1 .. Len(q)
                BY <3>1 DEF sends
            <3>3. \A n \in 1 .. Len(q) :
                     sends[n] = UnblockMsg(doc, q[n].id, q[n].address, t)
                BY <3>1 DEF sends
            <3>4. QED
                BY <3>2, <3>3 DEF Range
        <2>6. Range(sends) = MsgN(doc, P, t)
            BY <2>4, <2>5 DEF MsgN
        <2>7. sends \in Seq(Range(sends))
            <3>1. Len(q) \in Nat
                BY LenProperties
            <3>2. \A n \in 1 .. Len(q) : sends[n] \in Range(sends)
                BY <2>5, <3>1 DEF sends, Range
            <3>3. QED
                BY <3>1, <3>2, IsASeq DEF sends
        <2>8. \A i, j \in 1 .. Len(sends) :
                 i /= j => MsgKey(sends[i]) /= MsgKey(sends[j])
            <3>1. Len(sends) = Len(q)
                BY LenProperties DEF sends
            <3>2. \A n \in 1 .. Len(q) :
                     sends[n] = UnblockMsg(doc, q[n].id, q[n].address, t)
                BY LenProperties DEF sends
            <3>3. \A i, j \in 1 .. Len(q) :
                     i /= j =>
                       MsgKey(UnblockMsg(doc, q[i].id, q[i].address, t))
                         /= MsgKey(UnblockMsg(doc, q[j].id, q[j].address, t))
                BY <1>1, ListenKeys
            <3>4. QED
                BY <3>1, <3>2, <3>3
        <2>9. Deliver(b, sends) = Posted(b, Range(sends))
            BY <2>7, <2>8, DeliverPosted
        <2>10. QED
            BY <2>3, <2>6, <2>9 DEF BoxN
    <1>4. QED
        BY <1>2, <1>3

LEMMA QuietSends ==
    ASSUME NEW doc, NEW t
    PROVE  /\ SweepTimeoutAt(doc, t).sends = << >>
           /\ SweepCallbacks(doc, t).sends = << >>
           /\ SweepExpiresAt(doc, t).sends = << >>
PROOF
    <1>1. SweepTimeoutAt(doc, t).sends = << >>
        <2> DEFINE due ==
                { i \in DOMAIN doc :
                    doc[i].promise.state = "pending"
                    /\ doc[i].promise.timeoutAt <= t }
        <2>1. CASE due = {}
            <3> DEFINE r ==
                    [ doc |-> doc, puts |-> << >>, dels |-> << >>, sends |-> << >> ]
            <3>1. SweepTimeoutAt(doc, t) = r
                BY <2>1, Isa DEF SweepTimeoutAt, due, r
            <3>2. QED
                BY <3>1 DEF r
        <2>2. CASE due # {}
            <3> DEFINE qp == SetToSeq(due)
            <3> DEFINE ql ==
                    SetToSeq({ i \in due : doc[i].task.state = "acquired" })
            <3> DEFINE qr ==
                    SetToSeq({ i \in due : doc[i].task.state = "pending" })
            <3> DEFINE r ==
                    [ doc   |-> [ i \in DOMAIN doc |->
                                    IF i \in due THEN Project(doc[i], t)
                                    ELSE doc[i] ],
                      puts  |-> << >>,
                      dels  |->    [ n \in 1 .. Len(qp) |->
                                       [ at   |-> doc[qp[n]].promise.timeoutAt,
                                         id   |-> qp[n],
                                         kind |-> "promise" ] ]
                                \o [ n \in 1 .. Len(ql) |->
                                       [ at   |-> doc[ql[n]].task.leaseTimeoutAt,
                                         id   |-> ql[n],
                                         kind |-> "lease" ] ]
                                \o [ n \in 1 .. Len(qr) |->
                                       [ at   |-> doc[qr[n]].task.retryTimeoutAt,
                                         id   |-> qr[n],
                                         kind |-> "retry" ] ],
                      sends |-> << >> ]
            <3>1. SweepTimeoutAt(doc, t) = r
                BY <2>2, Isa DEF SweepTimeoutAt, due, qp, ql, qr, r
            <3>2. QED
                BY <3>1 DEF r
        <2>3. QED
            BY <2>1, <2>2
    <1>2. SweepCallbacks(doc, t).sends = << >>
        <2> DEFINE S ==
                { x \in [id : { i \in DOMAIN doc :
                                  doc[i].promise.state /= "pending" },
                         awaiter : Id] :
                    x.awaiter \in doc[x.id].promise.callbacks }
        <2> DEFINE Resumes(w) == { x.id : x \in { y \in S : y.awaiter = w } }
        <2> DEFINE Woken == { x.awaiter : x \in S } \cap DOMAIN doc
        <2>1. LET P ==
                    { x \in [id : { i \in DOMAIN doc :
                                      doc[i].promise.state /= "pending" },
                             awaiter : Id] :
                        x.awaiter \in doc[x.id].promise.callbacks }
                  Resumes(w) == { x.id : x \in { y \in P : y.awaiter = w } }
                  Woken == { x.awaiter : x \in P } \cap DOMAIN doc
              IN  SweepCallbacks(doc, t).sends
                    = IF P = {} THEN << >> ELSE << >>
            BY ONLY DEF SweepCallbacks
        <2>2. SweepCallbacks(doc, t).sends = IF S = {} THEN << >> ELSE << >>
            BY <2>1 DEF S, Resumes, Woken
        <2>3. (IF S = {} THEN << >> ELSE << >>) = << >>
            OBVIOUS
        <2>4. QED
            BY <2>2, <2>3
    <1>3. SweepExpiresAt(doc, t).sends = << >>
        <2> DEFINE held ==
                { i \in DOMAIN doc :
                    doc[i].task.state = "acquired"
                    /\ doc[i].task.leaseTimeoutAt <= t }
        <2>1. CASE held = {}
            <3> DEFINE r ==
                    [ doc |-> doc, puts |-> << >>, dels |-> << >>, sends |-> << >> ]
            <3>1. SweepExpiresAt(doc, t) = r
                BY <2>1, Isa DEF SweepExpiresAt, held, r
            <3>2. QED
                BY <3>1 DEF r
        <2>2. CASE held # {}
            <3> DEFINE q == SetToSeq(held)
            <3> DEFINE r ==
                    [ doc   |-> [ i \in DOMAIN doc |->
                                    IF i \in held THEN
                                        [ doc[i] EXCEPT !.task.state = "pending",
                                                        !.task.pid = NoPid,
                                                        !.task.ttl = NoTime,
                                                        !.task.leaseTimeoutAt = NoTime,
                                                        !.task.retryTimeoutAt = t ]
                                    ELSE doc[i] ],
                      puts  |-> [ n \in 1 .. Len(q) |->
                                    [at |-> t, id |-> q[n], kind |-> "retry"] ],
                      dels  |-> [ n \in 1 .. Len(q) |->
                                    [ at   |-> doc[q[n]].task.leaseTimeoutAt,
                                      id   |-> q[n],
                                      kind |-> "lease" ] ],
                      sends |-> << >> ]
            <3>1. SweepExpiresAt(doc, t) = r
                BY <2>2, Isa DEF SweepExpiresAt, held, q, r
            <3>2. QED
                BY <3>1 DEF r
        <2>3. QED
            BY <2>1, <2>2
    <1>4. QED
        BY <1>1, <1>2, <1>3

LEMMA SweepSends ==
    ASSUME NEW doc, NEW t, NEW E,
           NEW heard \in Seq(E), NEW retried \in Seq(E),
           heard = SweepListeners(SweepTimeoutAt(doc, t).doc, t).sends,
           retried
             = SweepRetryAt(SweepExpiresAt(
                   SweepCallbacks(
                       SweepListeners(SweepTimeoutAt(doc, t).doc, t).doc, t).doc,
                   t).doc, t).sends
    PROVE  Sweep(doc, t).sends = heard \o retried
PROOF
    <1> DEFINE tmo == SweepTimeoutAt(doc, t)
    <1> DEFINE lis == SweepListeners(tmo.doc, t)
    <1> DEFINE cb == SweepCallbacks(lis.doc, t)
    <1> DEFINE ex == SweepExpiresAt(cb.doc, t)
    <1> DEFINE ry == SweepRetryAt(ex.doc, t)
    <1> DEFINE s2 == Merge(tmo, lis)
    <1> DEFINE s3 == Merge(s2, cb)
    <1> DEFINE s4 == Merge(s3, ex)
    <1> DEFINE s5 == Merge(s4, ry)
    <1> DEFINE a1 == SweepTimeoutAt(doc, t)
    <1> DEFINE a2 == Merge(a1, SweepListeners(a1.doc, t))
    <1> DEFINE a3 == Merge(a2, SweepCallbacks(a2.doc, t))
    <1> DEFINE a4 == Merge(a3, SweepExpiresAt(a3.doc, t))
    <1> DEFINE a5 == Merge(a4, SweepRetryAt(a4.doc, t))
    <1>1. Sweep(doc, t) = a5
        <2>1. Sweep(doc, t)
                 = LET s1 == SweepTimeoutAt(doc, t)
                       u2 == Merge(s1, SweepListeners(s1.doc, t))
                       u3 == Merge(u2, SweepCallbacks(u2.doc, t))
                       u4 == Merge(u3, SweepExpiresAt(u3.doc, t))
                   IN  Merge(u4, SweepRetryAt(u4.doc, t))
            BY DEF Sweep
        <2>2. QED
            BY <2>1, Isa DEF a1, a2, a3, a4, a5
    <1>1a. a1 = tmo
        BY DEF a1, tmo
    <1>1b. a2 = s2
        BY <1>1a DEF a2, s2, lis
    <1>1c. a2.doc = lis.doc
        BY <1>1b DEF s2, Merge
    <1>1d. SweepCallbacks(a2.doc, t) = cb
        BY <1>1c DEF cb
    <1>1e. a3 = s3
        BY <1>1b, <1>1d DEF a3, s3
    <1>1f. a3.doc = cb.doc
        BY <1>1e DEF s3, Merge
    <1>1g. SweepExpiresAt(a3.doc, t) = ex
        BY <1>1f DEF ex
    <1>1h. a4 = s4
        BY <1>1e, <1>1g DEF a4, s4
    <1>1i. a4.doc = ex.doc
        BY <1>1h DEF s4, Merge
    <1>1j. SweepRetryAt(a4.doc, t) = ry
        BY <1>1i DEF ry
    <1>1k. a5 = s5
        BY <1>1h, <1>1j DEF a5, s5
    <1>2. /\ tmo.sends = << >>
          /\ cb.sends = << >>
          /\ ex.sends = << >>
        BY QuietSends DEF tmo, cb, ex
    <1>3. /\ heard = lis.sends
          /\ retried = ry.sends
        BY DEF tmo, lis, cb, ex, ry
    <1>4. << >> \in Seq(E)
        BY EmptySeq
    <1>5. s2.sends = tmo.sends \o lis.sends
        BY DEF s2, Merge
    <1>6. s2.sends = heard
        BY <1>2, <1>3, <1>4, <1>5, ConcatEmptySeq
    <1>7. s3.sends = s2.sends \o cb.sends
        BY DEF s3, Merge
    <1>8. s3.sends = heard
        BY <1>2, <1>4, <1>6, <1>7, ConcatEmptySeq
    <1>9. s4.sends = s3.sends \o ex.sends
        BY DEF s4, Merge
    <1>10. s4.sends = heard
        BY <1>2, <1>4, <1>8, <1>9, ConcatEmptySeq
    <1>11. s5.sends = s4.sends \o ry.sends
        BY DEF s5, Merge
    <1>12. Sweep(doc, t) = s5
        BY <1>1, <1>1k
    <1>13. QED
        BY <1>3, <1>10, <1>11, <1>12

LEMMA TagKey ==
    ASSUME NEW a, NEW c,
           a.message.tag = "Unblock",
           c.message.tag = "Execute"
    PROVE  MsgKey(a) /= MsgKey(c)
PROOF
    BY DEF MsgKey

LEMMA CatKeys ==
    ASSUME NEW E, NEW s1 \in Seq(E), NEW s2 \in Seq(E),
           \A i, j \in 1 .. Len(s1) :
              i /= j => MsgKey(s1[i]) /= MsgKey(s1[j]),
           \A i, j \in 1 .. Len(s2) :
              i /= j => MsgKey(s2[i]) /= MsgKey(s2[j]),
           \A i \in 1 .. Len(s1), j \in 1 .. Len(s2) :
              MsgKey(s1[i]) /= MsgKey(s2[j])
    PROVE  \A i, j \in 1 .. Len(s1 \o s2) :
               i /= j => MsgKey((s1 \o s2)[i]) /= MsgKey((s1 \o s2)[j])
PROOF
    <1>1. /\ Len(s1) \in Nat
          /\ Len(s2) \in Nat
          /\ Len(s1 \o s2) = Len(s1) + Len(s2)
          /\ \A i \in 1 .. (Len(s1) + Len(s2)) :
                (s1 \o s2)[i]
                   = IF i <= Len(s1) THEN s1[i] ELSE s2[i - Len(s1)]
        BY LenProperties, ConcatProperties
    <1>2. ASSUME NEW i \in 1 .. Len(s1 \o s2),
                 NEW j \in 1 .. Len(s1 \o s2),
                 i /= j
          PROVE  MsgKey((s1 \o s2)[i]) /= MsgKey((s1 \o s2)[j])
        <2> DEFINE n1 == Len(s1)
        <2> DEFINE n2 == Len(s2)
        <2>1. i \in 1 .. (n1 + n2) /\ j \in 1 .. (n1 + n2)
            BY <1>1, <1>2 DEF n1, n2
        <2>2. (s1 \o s2)[i] = IF i <= n1 THEN s1[i] ELSE s2[i - n1]
            BY <1>1, <2>1 DEF n1, n2
        <2>3. (s1 \o s2)[j] = IF j <= n1 THEN s1[j] ELSE s2[j - n1]
            BY <1>1, <2>1 DEF n1, n2
        <2>4. CASE i <= n1 /\ j <= n1
            BY <1>2, <2>2, <2>3, <2>4 DEF n1
        <2>5. CASE i <= n1 /\ j > n1
            <3>1. j - n1 \in 1 .. n2
                BY <1>1, <2>1, <2>5, Z3 DEF n1, n2
            <3>2. QED
                BY <2>2, <2>3, <2>5, <3>1 DEF n1
        <2>6. CASE i > n1 /\ j <= n1
            <3>1. i - n1 \in 1 .. n2
                BY <1>1, <2>1, <2>6, Z3 DEF n1, n2
            <3>2. QED
                BY <2>2, <2>3, <2>6, <3>1 DEF n1
        <2>7. CASE i > n1 /\ j > n1
            <3>1. i - n1 \in 1 .. n2 /\ j - n1 \in 1 .. n2 /\ i - n1 /= j - n1
                BY <1>1, <1>2, <2>1, <2>7, Z3 DEF n1, n2
            <3>2. QED
                BY <2>2, <2>3, <2>7, <3>1 DEF n1, n2
        <2>8. QED
            BY <2>4, <2>5, <2>6, <2>7, Z3 DEF n1
    <1>3. QED
        BY <1>2

LEMMA TwoPass ==
    ASSUME NEW b, NEW E, NEW s1 \in Seq(E), NEW s2 \in Seq(E),
           \A n \in 1 .. Len(s1) : s1[n].message.tag = "Unblock",
           \A n \in 1 .. Len(s2) : s2[n].message.tag = "Execute",
           \A i, j \in 1 .. Len(s1) :
              i /= j => MsgKey(s1[i]) /= MsgKey(s1[j]),
           \A i, j \in 1 .. Len(s2) :
              i /= j => MsgKey(s2[i]) /= MsgKey(s2[j])
    PROVE  Deliver(b, s1 \o s2) = Posted(b, Range(s1) \cup Range(s2))
PROOF
    <1>1. \A i \in 1 .. Len(s1), j \in 1 .. Len(s2) :
             MsgKey(s1[i]) /= MsgKey(s2[j])
        <2>1. ASSUME NEW i \in 1 .. Len(s1), NEW j \in 1 .. Len(s2)
              PROVE  MsgKey(s1[i]) /= MsgKey(s2[j])
            BY <2>1, TagKey
        <2>2. QED
            BY <2>1
    <1>2. \A i, j \in 1 .. Len(s1 \o s2) :
             i /= j => MsgKey((s1 \o s2)[i]) /= MsgKey((s1 \o s2)[j])
        BY <1>1, CatKeys
    <1>3. s1 \o s2 \in Seq(E)
        BY ConcatProperties
    <1>4. Deliver(b, s1 \o s2) = Posted(b, Range(s1 \o s2))
        BY <1>2, <1>3, DeliverPosted
    <1>5. Range(s1 \o s2) = Range(s1) \cup Range(s2)
        BY RangeConcatenation
    <1>6. QED
        BY <1>4, <1>5

=============================================================================
