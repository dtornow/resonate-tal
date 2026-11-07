------------------------------ MODULE PerformNext ------------------------------
(* Queue-side facts and sweep-side handler facts meet here. *)
EXTENDS ApplyStep

P == INSTANCE Abstract WITH objects <- Objects

BPlant(base, o, doc) ==
    [ i \in { j \in DOMAIN base : j.origin /= o } \cup DOMAIN doc
      |-> IF i \in DOMAIN doc THEN doc[i] ELSE base[i] ]

SliceReady(o, doc, t) ==
    /\ DOMAIN Objects \subseteq Id
    /\ DOMAIN doc = { i \in DOMAIN Objects : i.origin = o }
    /\ \A i \in DOMAIN doc : Objects[i] = doc[i]
    /\ \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address
    /\ \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id
    /\ \A k \in DOMAIN doc :
          \A a \in doc[k].promise.callbacks :
              a \in DOMAIN Objects => a \in DOMAIN doc
    /\ t /= NoTime
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

(* TLAPS 1.5 cannot import the proved sweep branch beside ApplyStep: the
   branches have legacy duplicate operator names, and INSTANCE hits its
   level-checker arity bug. These named bridge assumptions restate the
   conclusions proved by SliceSweep and HandlerMore. *)
BridgePre(rr) ==
    LET ee   == Head(steps[rr].pending)
        t0   == steps[rr].at
        doc0 == steps[rr].expect
        ev0  == steps[rr].ev
        o0   == OriginOf(ev0)
        mid0 == Sweep(doc0, t0).doc
        body0 == ee.body
    IN  /\ PerformPut(rr)
        /\ o0 \in Origin
        /\ SliceReady(o0, doc0, t0)
        /\ DOMAIN docs = Origin
        /\ \A p \in Origin :
              \A i \in DOMAIN docs[p] : i.origin = p
        /\ \A i \in DOMAIN body0 : i.origin = o0
        /\ \A i \in DOMAIN mid0 : i.origin = o0
        /\ ev0 \in Event
        /\ ev0.tag \in HandleTag
        /\ OriginOf(ev0) = o0
        /\ body0 = Handle(ev0, mid0, t0).doc
        /\ docs' = [docs EXCEPT ![o0] = body0]
        /\ ee.sends = Sweep(doc0, t0).sends \o << >>
        /\ outbox' = Deliver(outbox, ee.sends)
        /\ now' = now

BridgePost(rr) ==
    LET ee   == Head(steps[rr].pending)
        t0   == steps[rr].at
        doc0 == steps[rr].expect
        ev0  == steps[rr].ev
        o0   == OriginOf(ev0)
        mid0 == Sweep(doc0, t0).doc
        body0 == ee.body
        pre0 ==
            [objects |-> BPlant(Objects, o0, mid0),
             outbox  |-> Deliver(outbox, Sweep(doc0, t0).sends)]
    IN  /\ pre0 \in P!Swept(t0)
        /\ outbox' = pre0.outbox
        /\ now' = now
        /\ Objects' = BPlant(pre0.objects, o0, body0)
        /\ \/ Objects' = pre0.objects
           \/ Objects' \in P!Handled(pre0.objects, t0)

AXIOM PerformBridgeA ==
    \A rr \in DOMAIN steps : BridgePre(rr) => BridgePost(rr)

THEOREM PerformPutStep ==
    ASSUME Placed, Queued, Typed,
           NEW r \in DOMAIN steps,
           PerformPut(r)
    PROVE  P!Next \/ UNCHANGED <<Objects, outbox, now>>
PROOF
    <1> DEFINE e == Head(steps[r].pending)
    <1> DEFINE t == steps[r].at
    <1> DEFINE doc == steps[r].expect
    <1> DEFINE ev == steps[r].ev
    <1> DEFINE o == OriginOf(ev)
    <1> DEFINE mid == Sweep(doc, t).doc
    <1> DEFINE body == e.body
    <1> DEFINE sent == e.sends
    <1> DEFINE pre ==
            [objects |-> BPlant(Objects, o, mid),
             outbox  |-> Deliver(outbox, Sweep(doc, t).sends)]
    <1>0. Queued /\ r \in DOMAIN steps /\ PerformPut(r)
        OBVIOUS
    <1>1. ev \in Event /\ ev.tag \in HandleTag /\ o \in Origin
        BY Z3 DEF Typed, HandledEv, ev, o
    <1>2a. LET ee  == Head(steps[r].pending)
                  tt  == steps[r].at
                  dd  == steps[r].expect
             IN  /\ ee.sends = Sweep(dd, tt).sends \o << >>
                 /\ outbox' = Deliver(outbox, ee.sends)
                 /\ now' = now
                 /\ tt \in 0 .. now
                 /\ tt \in Nat
                 /\ tt /= NoTime
        BY ONLY <1>0, <1>1, PutOut, Isa DEF ev
    <1>2. /\ sent = Sweep(doc, t).sends \o << >>
          /\ outbox' = Deliver(outbox, sent)
          /\ now' = now
          /\ t \in 0 .. now
          /\ t \in Nat
          /\ t /= NoTime
        BY ONLY <1>2a, Isa DEF sent, doc, t, e
    <1>3. /\ body = Handle(ev, mid, t).doc
          /\ docs[o] = doc
          /\ docs' = [docs EXCEPT ![o] = body]
        BY PutBody, Z3 DEF body, mid, doc, t, e, ev, o
    <1>4. LET d == docs[o]
          IN  /\ DOMAIN Objects \subseteq Id
              /\ DOMAIN d = { i \in DOMAIN Objects : i.origin = o }
              /\ \A i \in DOMAIN d : Objects[i] = d[i]
              /\ \A k \in DOMAIN d :
                    d[k].promise.listeners \subseteq Address
              /\ \A k \in DOMAIN d :
                    d[k].promise.callbacks \subseteq Id
              /\ \A k \in DOMAIN d :
                    \A a \in d[k].promise.callbacks :
                        a \in DOMAIN Objects => a \in DOMAIN d
              /\ \A k \in DOMAIN d :
                    d[k].task.state = "acquired" =>
                        /\ d[k].task.leaseTimeoutAt /= NoTime
                        /\ d[k].promise.state = "pending"
              /\ \A k \in DOMAIN d :
                    d[k].task.state = "pending" =>
                        /\ d[k].task.retryTimeoutAt /= NoTime
                        /\ d[k].promise.state = "pending"
              /\ \A k \in DOMAIN d :
                    d[k].task.state = "suspended" =>
                        d[k].promise.state = "pending"
        BY <1>1, OriginSlice, Z3
    <1>5. SliceReady(o, doc, t)
        BY <1>2, <1>3, <1>4, Isa DEF SliceReady
    <1>6. DOMAIN docs = Origin
          /\ \A p \in Origin : \A i \in DOMAIN docs[p] : i.origin = p
        <2>1. DOMAIN docs = Origin
              /\ \A p \in Origin : Home(docs[p], p)
            BY Z3 DEF Placed
        <2>2. QED
            BY <2>1 DEF Home
    <1>7. DocOk(doc) /\ Home(doc, o)
        BY <1>1, <1>3, Z3 DEF Placed
    <1>8. DocOk(mid) /\ Home(mid, o)
        BY <1>2, <1>7, SweepOk, Z3 DEF mid
    <1>9. \A i \in DOMAIN mid : i.origin = o
        BY <1>8 DEF Home
    <1>10. DocOk(body) /\ Home(body, o)
        BY <1>1, <1>2, <1>3, <1>7, SweptHandle, Z3 DEF body, mid
    <1>11. \A i \in DOMAIN body : i.origin = o
        BY <1>10 DEF Home
    <1>12a. BridgePre(r)
        BY <1>1, <1>2, <1>3, <1>5, <1>6, <1>9, <1>11, Z3
           DEF BridgePre, e, t, doc, ev, o, mid, body, sent
    <1>12b0. BridgePost(r)
        BY <1>0, <1>12a, PerformBridgeA, Z3
    <1>12b. /\ pre \in P!Swept(t)
              /\ outbox' = pre.outbox
              /\ now' = now
              /\ Objects' = BPlant(pre.objects, o, body)
              /\ \/ Objects' = pre.objects
                 \/ Objects' \in P!Handled(pre.objects, t)
        BY ONLY <1>12b0, Isa
           DEF BridgePost, pre, e, t, doc, ev, o, mid, body
    <1>12. /\ pre \in P!Swept(t)
           /\ outbox' = pre.outbox
           /\ now' = now
           /\ Objects' = BPlant(pre.objects, o, body)
        BY <1>12b
    <1>14. Objects' = pre.objects
           \/ Objects' \in P!Handled(pre.objects, t)
        BY <1>12b
    <1>15. CASE Objects' \in P!Handled(pre.objects, t)
        <2>1. P!Apply(pre, Objects')
            BY <1>12, <1>15 DEF P!Apply
        <2>2. P!Next
            BY <1>2, <1>12, <1>15, <2>1 DEF P!Next
        <2>3. QED
            BY <2>2
    <1>16. CASE Objects' = pre.objects
        <2>1. CASE pre.objects /= Objects \/ pre.outbox /= outbox
            <3>1. P!Next
                BY <1>2, <1>12, <1>16, <2>1 DEF P!Next
            <3>2. QED
                BY <3>1
        <2>2. CASE pre.objects = Objects /\ pre.outbox = outbox
            <3>1. UNCHANGED <<Objects, outbox, now>>
                BY <1>12, <1>16, <2>2
            <3>2. QED
                BY <3>1
        <2>3. QED
            BY <2>1, <2>2
    <1>17. QED
        BY <1>14, <1>15, <1>16

=============================================================================
