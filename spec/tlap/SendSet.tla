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

=============================================================================
