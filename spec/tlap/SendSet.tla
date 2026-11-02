----------------------------- MODULE SendSet -----------------------------
(* A retry pass lists one Execute per due id. Delivery posts that set,
   whatever order SetToSeq picked. The enumeration facts are assumptions
   here; ToSeq proves them, and a single module cannot cite both. *)
EXTENDS Retry, Outbox

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

=============================================================================
