------------------------------ MODULE PassTag ------------------------------
(* A sweep pass writes the tag into the send record itself. Once the due
   set is finite, SetToSeq lays those records out as an injective sequence,
   so the message keys on that sequence are distinct. *)
EXTENDS Concrete, ToSeq, SequenceTheorems, TLAPS

LEMMA LitAt ==
    ASSUME NEW k \in Nat, NEW e(_), NEW i \in 1 .. k
    PROVE  [j \in 1 .. k |-> e(j)][i] = e(i)
PROOF
    BY Isa, Z3

LEMMA DomCtor ==
    ASSUME NEW D, NEW e(_)
    PROVE  DOMAIN [x \in D |-> e(x)] = D
PROOF
    BY Isa

LEMMA IntEq ==
    ASSUME NEW a \in Nat, NEW b \in Nat, (1 .. a) = (1 .. b)
    PROVE  a = b
PROOF
    BY Z3

LEMMA ListenShape ==
    ASSUME NEW doc, NEW t
    PROVE  LET pairs ==
                 { x \in [id : { i \in DOMAIN doc :
                                   doc[i].promise.state /= "pending" },
                          address : Address] :
                     x.address \in doc[x.id].promise.listeners }
               q == SetToSeq(pairs)
           IN  SweepListeners(doc, t).sends
                 = IF pairs = {} THEN << >>
                   ELSE [ n \in 1 .. Len(q) |->
                            [ address |-> q[n].address,
                              message |-> [ tag   |-> "Unblock",
                                            id    |-> q[n].id,
                                            state |-> doc[q[n].id].promise.state ] ] ]
PROOF
    BY ONLY DEF SweepListeners

LEMMA RetryShape ==
    ASSUME NEW doc, NEW t
    PROVE  LET S ==
                 { i \in DOMAIN doc :
                     doc[i].task.state = "pending"
                     /\ doc[i].task.retryTimeoutAt <= t }
               q == SetToSeq(S)
           IN  SweepRetryAt(doc, t).sends
                 = IF S = {} THEN << >>
                   ELSE [ n \in 1 .. Len(q) |->
                            [ address |-> doc[q[n]].promise.tags.target,
                              message |-> [ tag     |-> "Execute",
                                            id      |-> q[n],
                                            version |-> doc[q[n]].task.version ] ] ]
PROOF
    BY ONLY DEF SweepRetryAt

LEMMA ListenTags ==
    ASSUME NEW doc, NEW t, NEW P,
           P = { x \in [id : { i \in DOMAIN doc :
                                 doc[i].promise.state /= "pending" },
                        address : Address] :
                   x.address \in doc[x.id].promise.listeners },
           IsFiniteSet(P)
    PROVE  \A n \in 1 .. Len(SweepListeners(doc, t).sends) :
              SweepListeners(doc, t).sends[n].message.tag = "Unblock"
PROOF
    <1> DEFINE q == SetToSeq(P)
    <1> DEFINE e(n) ==
            [ address |-> q[n].address,
              message |-> [ tag   |-> "Unblock",
                            id    |-> q[n].id,
                            state |-> doc[q[n].id].promise.state ] ]
    <1> DEFINE raw == [n \in 1 .. Len(q) |-> e(n)]
    <1> DEFINE open ==
            [ n \in 1 .. Len(q) |->
                [ address |-> q[n].address,
                  message |-> [ tag   |-> "Unblock",
                                id    |-> q[n].id,
                                state |-> doc[q[n].id].promise.state ] ] ]
    <1>1. SweepListeners(doc, t).sends
            = IF P = {} THEN << >> ELSE open
        BY ListenShape
    <1>2. /\ q \in Seq(P)
          /\ Len(q) \in Nat
        <2>1. q \in Seq(P)
            BY SetToSeqAny DEF q
        <2>2. QED
            BY <2>1, LenProperties
    <1>3. open = raw
        BY DEF open, raw, e
    <1>4. SweepListeners(doc, t).sends
            = IF P = {} THEN << >> ELSE raw
        BY <1>1, <1>3
    <1>5. CASE P = {}
        <2>1. SweepListeners(doc, t).sends = << >>
            BY <1>4, <1>5
        <2>2. Len(SweepListeners(doc, t).sends) = 0
            BY <2>1, EmptySeq
        <2>3. QED
            BY <2>2
    <1>6. CASE P # {}
        <2>1. SweepListeners(doc, t).sends = raw
            BY <1>4, <1>6
        <2>2. ASSUME NEW n \in 1 .. Len(q)
              PROVE  raw[n] = e(n) /\ e(n).message.tag = "Unblock"
            <3>1. raw[n] = e(n)
                BY <1>2, <2>2, LitAt DEF raw
            <3>2. e(n).message.tag = "Unblock"
                BY DEF e
            <3>3. QED
                BY <3>1, <3>2
        <2>3. \A n \in 1 .. Len(q) : raw[n].message.tag = "Unblock"
            BY <2>2
        <2> DEFINE Img == { e(n) : n \in 1 .. Len(q) }
        <2>4. \A n \in 1 .. Len(q) : e(n) \in Img
            BY DEF Img
        <2>5. raw \in Seq(Img)
            BY <1>2, <2>4, IsASeq DEF raw
        <2>6. /\ Len(raw) \in Nat
              /\ DOMAIN raw = 1 .. Len(raw)
            BY <2>5, LenProperties
        <2>7. DOMAIN [n \in 1 .. Len(q) |-> e(n)] = 1 .. Len(q)
            BY DomCtor
        <2>7b. DOMAIN raw = 1 .. Len(q)
            BY <2>7 DEF raw
        <2>8. Len(raw) = Len(q)
            BY <1>2, <2>6, <2>7b, IntEq
        <2>9. QED
            BY <2>1, <2>3, <2>8
    <1>7. QED
        BY <1>5, <1>6

LEMMA RecPair ==
    ASSUME NEW S, NEW x \in [id : S, address : Address]
    PROVE  x = [id |-> x.id, address |-> x.address]
PROOF
    BY Isa

LEMMA UnblockRecKey ==
    ASSUME NEW doc, NEW a, NEW c,
           a = [id |-> a.id, address |-> a.address],
           c = [id |-> c.id, address |-> c.address],
           a /= c
    PROVE  MsgKey([ address |-> a.address,
                    message |-> [ tag   |-> "Unblock",
                                  id    |-> a.id,
                                  state |-> doc[a.id].promise.state ] ])
             /= MsgKey([ address |-> c.address,
                         message |-> [ tag   |-> "Unblock",
                                       id    |-> c.id,
                                       state |-> doc[c.id].promise.state ] ])
PROOF
    <1> DEFINE ea ==
            [ address |-> a.address,
              message |-> [ tag   |-> "Unblock",
                            id    |-> a.id,
                            state |-> doc[a.id].promise.state ] ]
    <1> DEFINE ec ==
            [ address |-> c.address,
              message |-> [ tag   |-> "Unblock",
                            id    |-> c.id,
                            state |-> doc[c.id].promise.state ] ]
    <1>1. ea.message.tag = "Unblock" /\ ec.message.tag = "Unblock"
        BY DEF ea, ec
    <1>2. MsgKey(ea)
            = [kind |-> "unblock", id |-> a.id, address |-> a.address]
        BY <1>1 DEF MsgKey, ea
    <1>3. MsgKey(ec)
            = [kind |-> "unblock", id |-> c.id, address |-> c.address]
        BY <1>1 DEF MsgKey, ec
    <1>4. a.id /= c.id \/ a.address /= c.address
        BY Z3
    <1>5. [kind |-> "unblock", id |-> a.id, address |-> a.address]
            /= [kind |-> "unblock", id |-> c.id, address |-> c.address]
        BY <1>4
    <1>6. QED
        BY <1>2, <1>3, <1>5

LEMMA ExecRecKey ==
    ASSUME NEW doc, NEW i, NEW j, i /= j
    PROVE  MsgKey([ address |-> doc[i].promise.tags.target,
                    message |-> [ tag     |-> "Execute",
                                  id      |-> i,
                                  version |-> doc[i].task.version ] ])
             /= MsgKey([ address |-> doc[j].promise.tags.target,
                         message |-> [ tag     |-> "Execute",
                                       id      |-> j,
                                       version |-> doc[j].task.version ] ])
PROOF
    BY DEF MsgKey

LEMMA RetryTags ==
    ASSUME NEW doc, NEW t, NEW S,
           S = { i \in DOMAIN doc :
                   doc[i].task.state = "pending"
                   /\ doc[i].task.retryTimeoutAt <= t },
           IsFiniteSet(S)
    PROVE  \A n \in 1 .. Len(SweepRetryAt(doc, t).sends) :
              SweepRetryAt(doc, t).sends[n].message.tag = "Execute"
PROOF
    <1> DEFINE q == SetToSeq(S)
    <1> DEFINE e(n) ==
            [ address |-> doc[q[n]].promise.tags.target,
              message |-> [ tag     |-> "Execute",
                            id      |-> q[n],
                            version |-> doc[q[n]].task.version ] ]
    <1> DEFINE raw == [n \in 1 .. Len(q) |-> e(n)]
    <1> DEFINE open ==
            [ n \in 1 .. Len(q) |->
                [ address |-> doc[q[n]].promise.tags.target,
                  message |-> [ tag     |-> "Execute",
                                id      |-> q[n],
                                version |-> doc[q[n]].task.version ] ] ]
    <1>1. SweepRetryAt(doc, t).sends
            = IF S = {} THEN << >> ELSE open
        BY RetryShape
    <1>2. /\ q \in Seq(S)
          /\ Len(q) \in Nat
        <2>1. q \in Seq(S)
            BY SetToSeqAny DEF q
        <2>2. QED
            BY <2>1, LenProperties
    <1>3. open = raw
        BY DEF open, raw, e
    <1>4. SweepRetryAt(doc, t).sends
            = IF S = {} THEN << >> ELSE raw
        BY <1>1, <1>3
    <1>5. CASE S = {}
        <2>1. SweepRetryAt(doc, t).sends = << >>
            BY <1>4, <1>5
        <2>2. Len(SweepRetryAt(doc, t).sends) = 0
            BY <2>1, EmptySeq
        <2>3. QED
            BY <2>2
    <1>6. CASE S # {}
        <2>1. SweepRetryAt(doc, t).sends = raw
            BY <1>4, <1>6
        <2>2. ASSUME NEW n \in 1 .. Len(q)
              PROVE  raw[n] = e(n) /\ e(n).message.tag = "Execute"
            <3>1. raw[n] = e(n)
                BY <1>2, <2>2, LitAt DEF raw
            <3>2. e(n).message.tag = "Execute"
                BY DEF e
            <3>3. QED
                BY <3>1, <3>2
        <2>3. \A n \in 1 .. Len(q) : raw[n].message.tag = "Execute"
            BY <2>2
        <2> DEFINE Img == { e(n) : n \in 1 .. Len(q) }
        <2>4. \A n \in 1 .. Len(q) : e(n) \in Img
            BY DEF Img
        <2>5. raw \in Seq(Img)
            BY <1>2, <2>4, IsASeq DEF raw
        <2>6. /\ Len(raw) \in Nat
              /\ DOMAIN raw = 1 .. Len(raw)
            BY <2>5, LenProperties
        <2>7. DOMAIN [n \in 1 .. Len(q) |-> e(n)] = 1 .. Len(q)
            BY DomCtor
        <2>8. DOMAIN raw = 1 .. Len(q)
            BY <2>7 DEF raw
        <2>9. Len(raw) = Len(q)
            BY <1>2, <2>6, <2>8, IntEq
        <2>10. QED
            BY <2>1, <2>3, <2>9
    <1>7. QED
        BY <1>5, <1>6

LEMMA ListenDistinct ==
    ASSUME NEW doc, NEW t, NEW P,
           P = { x \in [id : { i \in DOMAIN doc :
                                 doc[i].promise.state /= "pending" },
                        address : Address] :
                   x.address \in doc[x.id].promise.listeners },
           IsFiniteSet(P)
    PROVE  \A i, j \in 1 .. Len(SweepListeners(doc, t).sends) :
              i /= j =>
                MsgKey(SweepListeners(doc, t).sends[i])
                  /= MsgKey(SweepListeners(doc, t).sends[j])
PROOF
    <1> DEFINE q == SetToSeq(P)
    <1> DEFINE e(n) ==
            [ address |-> q[n].address,
              message |-> [ tag   |-> "Unblock",
                            id    |-> q[n].id,
                            state |-> doc[q[n].id].promise.state ] ]
    <1> DEFINE raw == [n \in 1 .. Len(q) |-> e(n)]
    <1> DEFINE open ==
            [ n \in 1 .. Len(q) |->
                [ address |-> q[n].address,
                  message |-> [ tag   |-> "Unblock",
                                id    |-> q[n].id,
                                state |-> doc[q[n].id].promise.state ] ] ]
    <1>1. SweepListeners(doc, t).sends
            = IF P = {} THEN << >> ELSE open
        BY ListenShape
    <1>2. /\ q \in Seq(P)
          /\ IsInjective(q)
          /\ Len(q) \in Nat
        <2>1. q \in Seq(P) /\ IsInjective(q)
            BY SetToSeqAny DEF q
        <2>2. QED
            BY <2>1, LenProperties
    <1>3. open = raw
        BY DEF open, raw, e
    <1>4. SweepListeners(doc, t).sends
            = IF P = {} THEN << >> ELSE raw
        BY <1>1, <1>3
    <1>5. P \subseteq [id : DOMAIN doc, address : Address]
        BY Zenon
    <1>6. CASE P = {}
        <2>1. SweepListeners(doc, t).sends = << >>
            BY <1>4, <1>6
        <2>2. Len(SweepListeners(doc, t).sends) = 0
            BY <2>1, EmptySeq
        <2>3. QED
            BY <2>2
    <1>7. CASE P # {}
        <2>1. SweepListeners(doc, t).sends = raw
            BY <1>4, <1>7
        <2>2. ASSUME NEW n \in 1 .. Len(q)
              PROVE  raw[n] = e(n)
            BY <1>2, <2>2, LitAt DEF raw
        <2>3. \A n \in 1 .. Len(q) : raw[n] = e(n)
            BY <2>2
        <2> DEFINE Img == { e(n) : n \in 1 .. Len(q) }
        <2>4. \A n \in 1 .. Len(q) : e(n) \in Img
            BY DEF Img
        <2>5. raw \in Seq(Img)
            BY <1>2, <2>4, IsASeq DEF raw
        <2>6. /\ Len(raw) \in Nat
              /\ DOMAIN raw = 1 .. Len(raw)
            BY <2>5, LenProperties
        <2>7. DOMAIN [n \in 1 .. Len(q) |-> e(n)] = 1 .. Len(q)
            BY DomCtor
        <2>8. DOMAIN raw = 1 .. Len(q)
            BY <2>7 DEF raw
        <2>9. Len(raw) = Len(q)
            BY <1>2, <2>6, <2>8, IntEq
        <2>10. ASSUME NEW i \in 1 .. Len(q), NEW j \in 1 .. Len(q), i /= j
               PROVE  MsgKey(e(i)) /= MsgKey(e(j))
            <3>1. DOMAIN q = 1 .. Len(q)
                BY <1>2, LenProperties
            <3>2. q[i] /= q[j]
                BY <1>2, <2>10, <3>1 DEF IsInjective
            <3>3. q[i] \in P /\ q[j] \in P
                BY <1>2, <2>10, ElementOfSeq
            <3>4. q[i] \in [id : DOMAIN doc, address : Address]
                    /\ q[j] \in [id : DOMAIN doc, address : Address]
                BY <1>5, <3>3
            <3>5. q[i] = [id |-> q[i].id, address |-> q[i].address]
                BY <3>4, RecPair
            <3>6. q[j] = [id |-> q[j].id, address |-> q[j].address]
                BY <3>4, RecPair
            <3>7. e(i)
                    = [ address |-> q[i].address,
                        message |-> [ tag   |-> "Unblock",
                                      id    |-> q[i].id,
                                      state |-> doc[q[i].id].promise.state ] ]
                BY DEF e
            <3>8. e(j)
                    = [ address |-> q[j].address,
                        message |-> [ tag   |-> "Unblock",
                                      id    |-> q[j].id,
                                      state |-> doc[q[j].id].promise.state ] ]
                BY DEF e
            <3>9. QED
                BY <3>2, <3>5, <3>6, <3>7, <3>8, UnblockRecKey
        <2>11. \A i, j \in 1 .. Len(q) :
                  i /= j => MsgKey(raw[i]) /= MsgKey(raw[j])
            BY <2>3, <2>10
        <2>12. QED
            BY <2>1, <2>9, <2>11
    <1>8. QED
        BY <1>6, <1>7

LEMMA RetryDistinct ==
    ASSUME NEW doc, NEW t, NEW S,
           S = { i \in DOMAIN doc :
                   doc[i].task.state = "pending"
                   /\ doc[i].task.retryTimeoutAt <= t },
           IsFiniteSet(S)
    PROVE  \A i, j \in 1 .. Len(SweepRetryAt(doc, t).sends) :
              i /= j =>
                MsgKey(SweepRetryAt(doc, t).sends[i])
                  /= MsgKey(SweepRetryAt(doc, t).sends[j])
PROOF
    <1> DEFINE q == SetToSeq(S)
    <1> DEFINE e(n) ==
            [ address |-> doc[q[n]].promise.tags.target,
              message |-> [ tag     |-> "Execute",
                            id      |-> q[n],
                            version |-> doc[q[n]].task.version ] ]
    <1> DEFINE raw == [n \in 1 .. Len(q) |-> e(n)]
    <1> DEFINE open ==
            [ n \in 1 .. Len(q) |->
                [ address |-> doc[q[n]].promise.tags.target,
                  message |-> [ tag     |-> "Execute",
                                id      |-> q[n],
                                version |-> doc[q[n]].task.version ] ] ]
    <1>1. SweepRetryAt(doc, t).sends
            = IF S = {} THEN << >> ELSE open
        BY RetryShape
    <1>2. /\ q \in Seq(S)
          /\ IsInjective(q)
          /\ Len(q) \in Nat
        <2>1. q \in Seq(S) /\ IsInjective(q)
            BY SetToSeqAny DEF q
        <2>2. QED
            BY <2>1, LenProperties
    <1>3. open = raw
        BY DEF open, raw, e
    <1>4. SweepRetryAt(doc, t).sends
            = IF S = {} THEN << >> ELSE raw
        BY <1>1, <1>3
    <1>5. CASE S = {}
        <2>1. SweepRetryAt(doc, t).sends = << >>
            BY <1>4, <1>5
        <2>2. Len(SweepRetryAt(doc, t).sends) = 0
            BY <2>1, EmptySeq
        <2>3. QED
            BY <2>2
    <1>6. CASE S # {}
        <2>1. SweepRetryAt(doc, t).sends = raw
            BY <1>4, <1>6
        <2>2. ASSUME NEW n \in 1 .. Len(q)
              PROVE  raw[n] = e(n)
            BY <1>2, <2>2, LitAt DEF raw
        <2>3. \A n \in 1 .. Len(q) : raw[n] = e(n)
            BY <2>2
        <2> DEFINE Img == { e(n) : n \in 1 .. Len(q) }
        <2>4. \A n \in 1 .. Len(q) : e(n) \in Img
            BY DEF Img
        <2>5. raw \in Seq(Img)
            BY <1>2, <2>4, IsASeq DEF raw
        <2>6. /\ Len(raw) \in Nat
              /\ DOMAIN raw = 1 .. Len(raw)
            BY <2>5, LenProperties
        <2>7. DOMAIN [n \in 1 .. Len(q) |-> e(n)] = 1 .. Len(q)
            BY DomCtor
        <2>8. DOMAIN raw = 1 .. Len(q)
            BY <2>7 DEF raw
        <2>9. Len(raw) = Len(q)
            BY <1>2, <2>6, <2>8, IntEq
        <2>10. ASSUME NEW i \in 1 .. Len(q), NEW j \in 1 .. Len(q), i /= j
               PROVE  MsgKey(e(i)) /= MsgKey(e(j))
            <3>1. DOMAIN q = 1 .. Len(q)
                BY <1>2, LenProperties
            <3>2. q[i] /= q[j]
                BY <1>2, <2>10, <3>1 DEF IsInjective
            <3>3. e(i)
                    = [ address |-> doc[q[i]].promise.tags.target,
                        message |-> [ tag     |-> "Execute",
                                      id      |-> q[i],
                                      version |-> doc[q[i]].task.version ] ]
                BY DEF e
            <3>4. e(j)
                    = [ address |-> doc[q[j]].promise.tags.target,
                        message |-> [ tag     |-> "Execute",
                                      id      |-> q[j],
                                      version |-> doc[q[j]].task.version ] ]
                BY DEF e
            <3>5. QED
                BY <3>2, <3>3, <3>4, ExecRecKey
        <2>11. \A i, j \in 1 .. Len(q) :
                  i /= j => MsgKey(raw[i]) /= MsgKey(raw[j])
            BY <2>3, <2>10
        <2>12. QED
            BY <2>1, <2>9, <2>11
    <1>7. QED
        BY <1>5, <1>6

LEMMA ListenSomeSeq ==
    ASSUME NEW doc, NEW t, NEW P,
           P = { x \in [id : { i \in DOMAIN doc :
                                 doc[i].promise.state /= "pending" },
                        address : Address] :
                   x.address \in doc[x.id].promise.listeners },
           IsFiniteSet(P)
    PROVE  \E E : SweepListeners(doc, t).sends \in Seq(E)
PROOF
    <1> DEFINE q == SetToSeq(P)
    <1> DEFINE e(n) ==
            [ address |-> q[n].address,
              message |-> [ tag   |-> "Unblock",
                            id    |-> q[n].id,
                            state |-> doc[q[n].id].promise.state ] ]
    <1> DEFINE raw == [n \in 1 .. Len(q) |-> e(n)]
    <1> DEFINE open ==
            [ n \in 1 .. Len(q) |->
                [ address |-> q[n].address,
                  message |-> [ tag   |-> "Unblock",
                                id    |-> q[n].id,
                                state |-> doc[q[n].id].promise.state ] ] ]
    <1> DEFINE Img == { e(n) : n \in 1 .. Len(q) }
    <1>1. SweepListeners(doc, t).sends
            = IF P = {} THEN << >> ELSE open
        BY ListenShape
    <1>2. /\ q \in Seq(P)
          /\ Len(q) \in Nat
        <2>1. q \in Seq(P)
            BY SetToSeqAny DEF q
        <2>2. QED
            BY <2>1, LenProperties
    <1>3. open = raw
        BY DEF open, raw, e
    <1>4. SweepListeners(doc, t).sends
            = IF P = {} THEN << >> ELSE raw
        BY <1>1, <1>3
    <1>5. CASE P = {}
        <2>1. SweepListeners(doc, t).sends = << >>
            BY <1>4, <1>5
        <2>2. << >> \in Seq({})
            BY EmptySeq
        <2>3. QED
            BY <2>1, <2>2
    <1>6. CASE P # {}
        <2>1. SweepListeners(doc, t).sends = raw
            BY <1>4, <1>6
        <2>2. \A n \in 1 .. Len(q) : e(n) \in Img
            BY DEF Img
        <2>3. raw \in Seq(Img)
            BY <1>2, <2>2, IsASeq DEF raw
        <2>4. QED
            BY <2>1, <2>3
    <1>7. QED
        BY <1>5, <1>6

LEMMA RetrySomeSeq ==
    ASSUME NEW doc, NEW t, NEW S,
           S = { i \in DOMAIN doc :
                   doc[i].task.state = "pending"
                   /\ doc[i].task.retryTimeoutAt <= t },
           IsFiniteSet(S)
    PROVE  \E E : SweepRetryAt(doc, t).sends \in Seq(E)
PROOF
    <1> DEFINE q == SetToSeq(S)
    <1> DEFINE e(n) ==
            [ address |-> doc[q[n]].promise.tags.target,
              message |-> [ tag     |-> "Execute",
                            id      |-> q[n],
                            version |-> doc[q[n]].task.version ] ]
    <1> DEFINE raw == [n \in 1 .. Len(q) |-> e(n)]
    <1> DEFINE open ==
            [ n \in 1 .. Len(q) |->
                [ address |-> doc[q[n]].promise.tags.target,
                  message |-> [ tag     |-> "Execute",
                                id      |-> q[n],
                                version |-> doc[q[n]].task.version ] ] ]
    <1> DEFINE Img == { e(n) : n \in 1 .. Len(q) }
    <1>1. SweepRetryAt(doc, t).sends
            = IF S = {} THEN << >> ELSE open
        BY RetryShape
    <1>2. /\ q \in Seq(S)
          /\ Len(q) \in Nat
        <2>1. q \in Seq(S)
            BY SetToSeqAny DEF q
        <2>2. QED
            BY <2>1, LenProperties
    <1>3. open = raw
        BY DEF open, raw, e
    <1>4. SweepRetryAt(doc, t).sends
            = IF S = {} THEN << >> ELSE raw
        BY <1>1, <1>3
    <1>5. CASE S = {}
        <2>1. SweepRetryAt(doc, t).sends = << >>
            BY <1>4, <1>5
        <2>2. << >> \in Seq({})
            BY EmptySeq
        <2>3. QED
            BY <2>1, <2>2
    <1>6. CASE S # {}
        <2>1. SweepRetryAt(doc, t).sends = raw
            BY <1>4, <1>6
        <2>2. \A n \in 1 .. Len(q) : e(n) \in Img
            BY DEF Img
        <2>3. raw \in Seq(Img)
            BY <1>2, <2>2, IsASeq DEF raw
        <2>4. QED
            BY <2>1, <2>3
    <1>7. QED
        BY <1>5, <1>6

=============================================================================
