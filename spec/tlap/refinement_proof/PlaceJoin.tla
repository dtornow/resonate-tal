----------------------------- MODULE PlaceJoin -----------------------------
(* The queue says which document a perform step will write. That document
   is the handler applied to the sweep, so the write keeps Placed once the
   event is one the handler knows and the origin is an origin. Typed says
   every stored event is such an event. A step keeps Typed, and therefore
   keeps Placed, when a timeout it submits names an id. *)
EXTENDS Shape, PerformInv

LEMMA HeadAt ==
    ASSUME NEW seq,
           seq \in Seq(Range(seq)),
           seq # << >>
    PROVE  Head(seq) = seq[1] /\ 1 \in DOMAIN seq
PROOF
    <1>1. Head(seq) = seq[1]
        BY Z3 DEF Head
    <1>2. Len(seq) \in Nat \ {0}
        BY EmptySeq, Z3
    <1>3. DOMAIN seq = 1 .. Len(seq)
        BY LenProperties, Z3
    <1>4. 1 \in DOMAIN seq
        BY <1>2, <1>3, Z3
    <1>5. QED
        BY <1>1, <1>4, Z3

LEMMA HeadBody ==
    ASSUME NEW seq, NEW docb, NEW sent,
           seq \in Seq(Range(seq)),
           seq # << >>,
           Docs(seq, docb, sent),
           Head(seq).tag = "PutDocument"
    PROVE  Head(seq).body = docb
PROOF
    <1>1. Head(seq) = seq[1] /\ 1 \in DOMAIN seq
        BY HeadAt, Z3
    <1>2. seq[1].tag = "PutDocument"
        BY <1>1, Z3
    <1>3. seq[1].body = docb
        BY <1>1, <1>2, Z3 DEF Docs
    <1>4. QED
        BY <1>1, <1>3, Z3

LEMMA ImageDoc ==
    ASSUME NEW st
    PROVE  Image(st).doc
              = Handle(st.ev, Sweep(st.expect, st.at).doc, st.at).doc
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
        BY <1>2, Z3

LEMMA PutFromMatch ==
    ASSUME Placed, Queued,
           NEW r \in DOMAIN steps,
           PerformPut(r),
           steps[r].ev \in Event,
           steps[r].ev.tag \in HandleTag,
           OriginOf(steps[r].ev) \in Origin
    PROVE  Placed'
PROOF
    <1> DEFINE e == Head(steps[r].pending)
    <1> DEFINE o == OriginOf(steps[r].ev)
    <1>1. now \in Nat
        BY Z3 DEF Queued
    <1>2. steps[r].phase = "perform"
        BY Z3 DEF PerformPut
    <1>3. Match(steps[r], now)
        BY <1>2, Z3 DEF Queued
    <1>4. steps[r].at \in 0 .. now
        BY <1>3, Z3 DEF Match
    <1>5. steps[r].pending \in Seq(Range(steps[r].pending))
          /\ Docs(steps[r].pending, Image(steps[r]).doc, Image(steps[r]).sends)
        BY <1>3, Z3 DEF Match
    <1>6. steps[r].pending # << >> /\ e.tag = "PutDocument"
        BY PutWrite, Z3 DEF e, PerformPut
    <1>7. e.body = Image(steps[r]).doc
        BY <1>5, <1>6, HeadBody, Z3 DEF e
    <1>8. Image(steps[r]).doc
            = Handle(steps[r].ev,
                     Sweep(steps[r].expect, steps[r].at).doc,
                     steps[r].at).doc
        BY ImageDoc, Z3
    <1>9. e.body = Handle(steps[r].ev,
                          Sweep(steps[r].expect, steps[r].at).doc,
                          steps[r].at).doc
        BY <1>7, <1>8, Z3
    <1>10. HIDE DEF Sweep, Handle, PerformPut, Image
    <1>11. o \in Origin /\ e = Head(steps[r].pending)
        BY Z3 DEF e, o
    <1>12. QED
        BY <1>1, <1>4, <1>9, <1>11, PutKeeps, Isa DEF e, o

LEMMA PlaceWhen ==
    ASSUME Placed, Queued, [Next]_vars,
           \A r \in DOMAIN steps :
                PerformPut(r) =>
                    /\ steps[r].ev \in Event
                    /\ steps[r].ev.tag \in HandleTag
                    /\ OriginOf(steps[r].ev) \in Origin
    PROVE  Placed'
PROOF
    <1>1. CASE \A r \in DOMAIN steps : ~PerformPut(r)
        BY <1>1, PlaceQuiet, Z3
    <1>2. CASE \E r \in DOMAIN steps : PerformPut(r)
        <2>1. PICK r \in DOMAIN steps : PerformPut(r)
            BY <1>2, Z3
        <2>2. steps[r].ev \in Event
              /\ steps[r].ev.tag \in HandleTag
              /\ OriginOf(steps[r].ev) \in Origin
            BY <2>1, Z3
        <2>3. QED
            BY <2>1, <2>2, PutFromMatch, Z3
    <1>3. QED
        BY <1>1, <1>2, Z3

(* Tags whose origin is the id on the event. The other handled tags name
   that id inside a request, an action, or an awaited promise, and a
   heartbeat names an origin by itself. *)
IdTags ==
    {"TaskAcquire", "TaskFence", "TaskSuspend", "TaskFulfill",
     "TaskRelease", "TaskHalt",
     "TaskContinue", "Timeout"}

HandledEv(ev) ==
    /\ ev \in Event
    /\ ev.tag \in HandleTag
    /\ OriginOf(ev) \in Origin

Typed ==
    \A r \in DOMAIN steps : HandledEv(steps[r].ev)

LEMMA PlaceNext ==
    ASSUME Placed, Queued, Typed, [Next]_vars
    PROVE  Placed'
PROOF
    <1>1. \A r \in DOMAIN steps :
            PerformPut(r) =>
                /\ steps[r].ev \in Event
                /\ steps[r].ev.tag \in HandleTag
                /\ OriginOf(steps[r].ev) \in Origin
        BY Z3 DEF Typed, HandledEv
    <1>2. QED
        BY <1>1, PlaceWhen, Z3

LEMMA TypeInit ==
    ASSUME Init
    PROVE  Typed
PROOF
    <1>1. steps = << >>
        BY Z3 DEF Init, EmptyFn
    <1>2. << >> \in Seq(Nat) /\ Len(<< >>) = 0
        BY EmptySeq, Z3
    <1>3. DOMAIN steps = {}
        BY <1>1, <1>2, LenProperties, Z3
    <1>4. QED
        BY <1>3, Z3 DEF Typed

LEMMA ChooseOrig ==
    ASSUME Origin /= {}
    PROVE  (CHOOSE o \in Origin : TRUE) \in Origin
PROOF
    <1>1. \E o \in Origin : TRUE
        BY Z3
    <1>2. PICK c \in Origin : TRUE
        BY <1>1, Z3
    <1>3. QED
        BY <1>2, Zenon

LEMMA EvId ==
    ASSUME NEW ev \in Event, ev.tag \in IdTags
    PROVE  ev.id \in Id
PROOF
    <1>3. CASE ev.tag = "TaskAcquire"
        BY <1>3, Z3 DEF Event, ExternalEvent, InternalEvent, On
    <1>4. CASE ev.tag = "TaskFence"
        BY <1>4, Z3 DEF Event, ExternalEvent, InternalEvent, On
    <1>5. CASE ev.tag = "TaskSuspend"
        BY <1>5, Z3 DEF Event, ExternalEvent, InternalEvent, On
    <1>6. CASE ev.tag = "TaskFulfill"
        BY <1>6, Z3 DEF Event, ExternalEvent, InternalEvent, On
    <1>7. CASE ev.tag = "TaskRelease"
        BY <1>7, Z3 DEF Event, ExternalEvent, InternalEvent, On
    <1>8. CASE ev.tag = "TaskHalt"
        BY <1>8, Z3 DEF Event, ExternalEvent, InternalEvent, On
    <1>9. CASE ev.tag = "TaskContinue"
        BY <1>9, Z3 DEF Event, ExternalEvent, InternalEvent, On
    <1>10. CASE ev.tag = "Timeout"
        BY <1>10, Z3 DEF Event, ExternalEvent, InternalEvent, On
    <1>11. QED
        BY <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, Z3
           DEF IdTags

LEMMA SettleId ==
    ASSUME NEW ev \in Event, ev.tag = "PromiseSettle"
    PROVE  ev.req.id \in Id
PROOF
    <1>1. ev.req \in SettleReq
        BY Z3 DEF Event, ExternalEvent, InternalEvent, On
    <1>2. QED
        BY <1>1, Z3 DEF SettleReq

LEMMA CbId ==
    ASSUME NEW ev \in Event, ev.tag = "PromiseRegisterCallback"
    PROVE  ev.req.awaited \in Id
PROOF
    <1>1. ev.req \in CallbackReq
        BY Z3 DEF Event, ExternalEvent, InternalEvent, On
    <1>2. ev.req \in [awaited : Id, awaiter : Id]
        BY <1>1, Z3 DEF CallbackReq
    <1>3. QED
        BY <1>2, Z3

LEMMA LsId ==
    ASSUME NEW ev \in Event, ev.tag = "PromiseRegisterListener"
    PROVE  ev.awaited \in Id
PROOF
    BY Z3 DEF Event, ExternalEvent, InternalEvent, On

LEMMA FromId ==
    ASSUME NEW ev, ev.id \in Id, OriginOf(ev) = ev.id.origin
    PROVE  OriginOf(ev) \in Origin
PROOF
    <1>1. ev.id.origin \in Origin
        BY IdOrig, Z3
    <1>2. QED
        BY <1>1, Z3

LEMMA OrigIn ==
    ASSUME NEW ev \in Event, ev.tag \in HandleTag, Origin /= {}
    PROVE  OriginOf(ev) \in Origin
PROOF
    <1>1. CASE ev.tag \in IdTags
        <2>1. ev.id \in Id
            BY <1>1, EvId, Z3
        <2>4. CASE ev.tag = "TaskAcquire"
            <3>1. OriginOf(ev) = ev.id.origin
                BY <2>4, Z3 DEF OriginOf
            <3>2. QED
                BY <2>1, <3>1, FromId, Z3
        <2>5. CASE ev.tag = "TaskFence"
            <3>1. OriginOf(ev) = ev.id.origin
                BY <2>5, Z3 DEF OriginOf
            <3>2. QED
                BY <2>1, <3>1, FromId, Z3
        <2>6. CASE ev.tag = "TaskSuspend"
            <3>1. OriginOf(ev) = ev.id.origin
                BY <2>6, Z3 DEF OriginOf
            <3>2. QED
                BY <2>1, <3>1, FromId, Z3
        <2>7. CASE ev.tag = "TaskFulfill"
            <3>1. OriginOf(ev) = ev.id.origin
                BY <2>7, Z3 DEF OriginOf
            <3>2. QED
                BY <2>1, <3>1, FromId, Z3
        <2>8. CASE ev.tag = "TaskRelease"
            <3>1. OriginOf(ev) = ev.id.origin
                BY <2>8, Z3 DEF OriginOf
            <3>2. QED
                BY <2>1, <3>1, FromId, Z3
        <2>9. CASE ev.tag = "TaskHalt"
            <3>1. OriginOf(ev) = ev.id.origin
                BY <2>9, Z3 DEF OriginOf
            <3>2. QED
                BY <2>1, <3>1, FromId, Z3
        <2>10. CASE ev.tag = "TaskContinue"
            <3>1. OriginOf(ev) = ev.id.origin
                BY <2>10, Z3 DEF OriginOf
            <3>2. QED
                BY <2>1, <3>1, FromId, Z3
        <2>11. CASE ev.tag = "Timeout"
            <3>1. OriginOf(ev) = ev.id.origin
                BY <2>11, Z3 DEF OriginOf
            <3>2. QED
                BY <2>1, <3>1, FromId, Z3
        <2>12. QED
            BY <1>1, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10,
               <2>11, Z3 DEF IdTags
    <1>2. CASE ev.tag = "PromiseCreate"
        <2>1. ev.req \in CreateReq
            BY <1>2, CreateOf, Z3
        <2>2. ev.req.id \in Id
            BY <2>1, CreateId, Z3
        <2>3. ev.req.id.origin \in Origin
            BY <2>2, IdOrig, Z3
        <2>4. OriginOf(ev) = ev.req.id.origin
            BY <1>2, Z3 DEF OriginOf
        <2>5. QED
            BY <2>3, <2>4, Z3
    <1>3. CASE ev.tag = "PromiseSettle"
        <2>1. ev.req.id \in Id
            BY <1>3, SettleId, Z3
        <2>2. ev.req.id.origin \in Origin
            BY <2>1, IdOrig, Z3
        <2>3. OriginOf(ev) = ev.req.id.origin
            BY <1>3, Z3 DEF OriginOf
        <2>4. QED
            BY <2>2, <2>3, Z3
    <1>4. CASE ev.tag = "PromiseRegisterCallback"
        <2>1. ev.req.awaited \in Id
            BY <1>4, CbId, Z3
        <2>2. ev.req.awaited.origin \in Origin
            BY <2>1, IdOrig, Z3
        <2>3. OriginOf(ev) = ev.req.awaited.origin
            BY <1>4, Z3 DEF OriginOf
        <2>4. QED
            BY <2>2, <2>3, Z3
    <1>5. CASE ev.tag = "PromiseRegisterListener"
        <2>1. ev.awaited \in Id
            BY <1>5, LsId, Z3
        <2>2. ev.awaited.origin \in Origin
            BY <2>1, IdOrig, Z3
        <2>3. OriginOf(ev) = ev.awaited.origin
            BY <1>5, Z3 DEF OriginOf
        <2>4. QED
            BY <2>2, <2>3, Z3
    <1>6. CASE ev.tag = "TaskCreate"
        <2>1. ev.action \in CreateReq
            BY <1>6, TCreateOf, Z3
        <2>2. ev.action.id \in Id
            BY <2>1, CreateId, Z3
        <2>3. ev.action.id.origin \in Origin
            BY <2>2, IdOrig, Z3
        <2>4. OriginOf(ev) = ev.action.id.origin
            BY <1>6, Z3 DEF OriginOf
        <2>5. QED
            BY <2>3, <2>4, Z3
    <1>7. CASE ev.tag = "TaskHeartbeat"
        <2>1. Origin /= {}
            BY Z3
        <2>2. OriginOf(ev) = (CHOOSE o \in Origin : TRUE)
            BY <1>7, Z3 DEF OriginOf
        <2>3. (CHOOSE o \in Origin : TRUE) \in Origin
            BY <2>1, ChooseOrig, Z3
        <2>4. QED
            BY <2>2, <2>3, Z3
    <1>8. QED
        BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, Z3 DEF HandleTag, IdTags

LEMMA TagIn ==
    ASSUME NEW ev \in Event
    PROVE  ev.tag \in HandleTag
PROOF
    <1>2. CASE ev \in ExternalEvent
        BY <1>2, Z3 DEF ExternalEvent, On, HandleTag
    <1>3. CASE ev \in InternalEvent
        BY <1>3, Z3 DEF InternalEvent, On, HandleTag
    <1>4. QED
        BY <1>2, <1>3, Z3 DEF Event

LEMMA KnownEv ==
    ASSUME NEW ev \in Event,
           Origin /= {}
    PROVE  HandledEv(ev)
PROOF
    <1>2. Origin /= {}
        BY Z3
    <1>3. ev.tag \in HandleTag
        BY TagIn, Z3
    <1>4. OriginOf(ev) \in Origin
        BY <1>2, <1>3, OrigIn, Z3
    <1>5. QED
        BY <1>3, <1>4, Z3 DEF HandledEv

LEMMA TimeoutMem ==
    ASSUME NEW a \in Id, NEW b \in DeadlineKind, NEW rec,
           rec = [tag |-> "Timeout", id |-> a, kind |-> b]
    PROVE  rec \in { [tag |-> "Timeout", id |-> i, kind |-> k]
                     : i \in Id, k \in DeadlineKind }
PROOF
    BY Z3, IsaM("blast")

LEMMA TimeoutIn ==
    ASSUME NEW ii \in Id, NEW kk \in DeadlineKind, "Timeout" \in Implemented
    PROVE  /\ [tag |-> "Timeout", id |-> ii, kind |-> kk] \in Event
           /\ [tag |-> "Timeout", id |-> ii, kind |-> kk].tag = "Timeout"
           /\ [tag |-> "Timeout", id |-> ii, kind |-> kk].id = ii
PROOF
    <1> DEFINE nev == [tag |-> "Timeout", id |-> ii, kind |-> kk]
    <1> DEFINE S == { [tag |-> "Timeout", id |-> i, kind |-> k]
                      : i \in Id, k \in DeadlineKind }
    <1>1. ii \in Id /\ kk \in DeadlineKind /\ "Timeout" \in Implemented
        BY Z3
    <1>2. nev = [tag |-> "Timeout", id |-> ii, kind |-> kk]
        BY Zenon DEF nev
    <1>3. \E i \in Id, k \in DeadlineKind :
            nev = [tag |-> "Timeout", id |-> i, kind |-> k]
        BY <1>1, <1>2, Z3
    <1>4. PICK i \in Id, k \in DeadlineKind :
            nev = [tag |-> "Timeout", id |-> i, kind |-> k]
        BY <1>3, Z3
    <1>5. nev \in { [tag |-> "Timeout", id |-> i, kind |-> k]
                    : i \in Id, k \in DeadlineKind }
        BY <1>4, TimeoutMem, Z3
    <1>6. S = { [tag |-> "Timeout", id |-> i, kind |-> k]
                : i \in Id, k \in DeadlineKind }
        BY ONLY DEF S
    <1>7. nev \in S
        BY <1>5, <1>6, Z3
    <1>8. On("Timeout", S) = S
        BY <1>1, Z3 DEF On
    <1>9. nev \in InternalEvent
        BY <1>7, <1>8, Z3 DEF InternalEvent, S
    <1>10. nev.tag = "Timeout" /\ nev.id = ii
        BY <1>2, Zenon
    <1>11. QED
        BY <1>9, <1>10, Z3 DEF Event, nev

(* The event on a step record is unchanged when the domain is unchanged
   and every other record is the old record. *)
LEMMA EvStay ==
    ASSUME Typed,
           NEW r \in DOMAIN steps,
           DOMAIN steps' = DOMAIN steps,
           steps'[r].ev = steps[r].ev,
           \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
    PROVE  Typed'
PROOF
    <1>1. ASSUME NEW q \in DOMAIN steps'
          PROVE  HandledEv(steps'[q].ev)
        <2>1. q \in DOMAIN steps
            BY <1>1, Z3
        <2>2. CASE q = r
            <3>1. steps'[q].ev = steps[q].ev
                BY <2>2, Z3
            <3>2. HandledEv(steps[q].ev)
                BY <2>1, Z3 DEF Typed
            <3>3. QED
                BY <3>1, <3>2, Z3
        <2>3. CASE q # r
            <3>1. steps'[q] = steps[q]
                BY <2>1, <2>3, Z3
            <3>2. HandledEv(steps[q].ev)
                BY <2>1, Z3 DEF Typed
            <3>3. steps'[q].ev = steps[q].ev
                BY <3>1, Z3
            <3>4. QED
                BY <3>2, <3>3, Z3
        <2>4. QED
            BY <2>2, <2>3, Z3
    <1>2. QED
        BY <1>1, Z3 DEF Typed

LEMMA StayTyped ==
    ASSUME Typed, steps' = steps
    PROVE  Typed'
PROOF
    BY Isa DEF Typed

LEMMA OneTyped ==
    ASSUME Typed, Shaped,
           NEW r \in DOMAIN steps,
           NEW e,
           steps' = [steps EXCEPT ![r].pending = e]
    PROVE  Typed'
PROOF
    <1>1. DOMAIN steps[r] = StepDom
        BY Zenon DEF Shaped
    <1>2. ASSUME NEW rr \in DOMAIN steps, NEW ee,
                 /\ rr = r
                 /\ ee = e
                 /\ DOMAIN steps[rr] = StepDom
                 /\ steps' = [steps EXCEPT ![rr].pending = ee]
          PROVE  steps'[rr].ev = steps[rr].ev /\ DOMAIN steps' = DOMAIN steps
        BY <1>2, PendingAt, Zenon
    <1>3. steps'[r].ev = steps[r].ev /\ DOMAIN steps' = DOMAIN steps
        BY <1>1, <1>2, Zenon
    <1>4. \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
        BY Zenon
    <1>5. Typed /\ r \in DOMAIN steps
        BY Zenon
    <1>6. QED
        BY ONLY <1>3, <1>4, <1>5, EvStay, Zenon

LEMMA MissTyped ==
    ASSUME Typed, Shaped,
           NEW r \in DOMAIN steps,
           steps' = [steps EXCEPT ![r].phase = "process",
                                  ![r].pending = << >>]
    PROVE  Typed'
PROOF
    <1>1. "phase" \in DOMAIN steps[r] /\ "at" \in DOMAIN steps[r]
          /\ "pending" \in DOMAIN steps[r] /\ "expect" \in DOMAIN steps[r]
          /\ "ev" \in DOMAIN steps[r]
        BY Zenon DEF Shaped, StepDom
    <1>2. /\ steps'[r].phase = "process"
          /\ steps'[r].pending = << >>
          /\ steps'[r].at = steps[r].at
          /\ steps'[r].expect = steps[r].expect
          /\ steps'[r].ev = steps[r].ev
          /\ DOMAIN steps' = DOMAIN steps
          /\ DOMAIN steps'[r] = DOMAIN steps[r]
        <2>1. SUFFICES ASSUME steps' = [steps EXCEPT ![r].phase = "process",
                                                     ![r].pending = << >>],
                              r \in DOMAIN steps,
                              "phase" \in DOMAIN steps[r],
                              "at" \in DOMAIN steps[r],
                              "pending" \in DOMAIN steps[r],
                              "expect" \in DOMAIN steps[r],
                              "ev" \in DOMAIN steps[r]
                       PROVE  /\ steps'[r].phase = "process"
                              /\ steps'[r].pending = << >>
                              /\ steps'[r].at = steps[r].at
                              /\ steps'[r].expect = steps[r].expect
                              /\ steps'[r].ev = steps[r].ev
                              /\ DOMAIN steps' = DOMAIN steps
                              /\ DOMAIN steps'[r] = DOMAIN steps[r]
            BY <1>1, Zenon
        <2>2. QED
            BY <2>1, MissAt, Isa
    <1>3. \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
        BY Zenon
    <1>4. Typed /\ r \in DOMAIN steps
        BY Zenon
    <1>5. QED
        BY ONLY <1>2, <1>3, <1>4, EvStay, Zenon

LEMMA FourTyped ==
    ASSUME Typed, Shaped,
           NEW r \in DOMAIN steps,
           NEW a, NEW b, NEW c, NEW d,
           steps' = [steps EXCEPT ![r].phase = a, ![r].at = b,
                                    ![r].pending = c, ![r].expect = d]
    PROVE  Typed'
PROOF
    <1>1. "phase" \in DOMAIN steps[r] /\ "at" \in DOMAIN steps[r]
          /\ "pending" \in DOMAIN steps[r] /\ "expect" \in DOMAIN steps[r]
          /\ "ev" \in DOMAIN steps[r]
        BY Zenon DEF Shaped, StepDom
    <1>2. /\ steps'[r].phase = a
          /\ steps'[r].at = b
          /\ steps'[r].pending = c
          /\ steps'[r].expect = d
          /\ steps'[r].ev = steps[r].ev
          /\ DOMAIN steps' = DOMAIN steps
          /\ DOMAIN steps'[r] = DOMAIN steps[r]
        <2>1. SUFFICES ASSUME steps' = [steps EXCEPT ![r].phase = a, ![r].at = b,
                                                     ![r].pending = c, ![r].expect = d],
                              r \in DOMAIN steps,
                              "phase" \in DOMAIN steps[r],
                              "at" \in DOMAIN steps[r],
                              "pending" \in DOMAIN steps[r],
                              "expect" \in DOMAIN steps[r],
                              "ev" \in DOMAIN steps[r]
                       PROVE  /\ steps'[r].phase = a
                              /\ steps'[r].at = b
                              /\ steps'[r].pending = c
                              /\ steps'[r].expect = d
                              /\ steps'[r].ev = steps[r].ev
                              /\ DOMAIN steps' = DOMAIN steps
                              /\ DOMAIN steps'[r] = DOMAIN steps[r]
            BY <1>1, Zenon
        <2>2. QED
            BY <2>1, FourAt, Isa
    <1>3. \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
        BY Zenon
    <1>4. Typed /\ r \in DOMAIN steps
        BY Zenon
    <1>5. QED
        BY ONLY <1>2, <1>3, <1>4, EvStay, Zenon

LEMMA DelTyped ==
    ASSUME Typed, NEW r \in DOMAIN steps, steps' = Del(steps, r)
    PROVE  Typed'
PROOF
    <1>1. ASSUME NEW q \in DOMAIN steps'
          PROVE  q \in DOMAIN steps /\ q # r /\ steps'[q] = steps[q]
        BY <1>1, Zenon DEF Del
    <1>2. ASSUME NEW q \in DOMAIN steps'
          PROVE  HandledEv(steps'[q].ev)
        <2>1. q \in DOMAIN steps /\ steps'[q] = steps[q]
            BY <1>1, <1>2, Zenon
        <2>2. steps'[q].ev = steps[q].ev
            BY ONLY <2>1, Z3
        <2>3. Typed
            BY Zenon
        <2>4. HandledEv(steps[q].ev)
            BY ONLY <2>1, <2>3, Z3 DEF Typed
        <2>5. QED
            BY ONLY <2>2, <2>4, Z3
    <1>3. QED
        BY <1>2, Zenon DEF Typed

LEMMA AddTyped ==
    ASSUME Typed,
           NEW r, NEW ev,
           HandledEv(ev),
           r \notin DOMAIN steps,
           steps' = Set(steps, r, Fresh(ev))
    PROVE  Typed'
PROOF
    <1>1. steps'[r] = Fresh(ev)
        BY Zenon DEF Set
    <1>2. DOMAIN steps' = (DOMAIN steps) \cup {r}
        BY Zenon DEF Set
    <1>3. Fresh(ev).ev = ev
        <2>1. ASSUME NEW ee, NEW pp, NEW xx, NEW tt, NEW rc,
                     /\ ee = ev
                     /\ pp = << >>
                     /\ xx = EmptyFn
                     /\ tt = NoTime
                     /\ rc = [ev |-> ee, phase |-> "process", pending |-> pp,
                              expect |-> xx, at |-> tt]
              PROVE  rc.ev = ee
            BY <2>1, DomRec, Zenon
        <2>2. Fresh(ev) = [ev |-> ev, phase |-> "process", pending |-> << >>,
                           expect |-> EmptyFn, at |-> NoTime]
            BY Zenon DEF Fresh
        <2>3. QED
            BY <2>1, <2>2, Zenon
    <1>4. steps'[r].ev = ev
        BY <1>1, <1>3, Zenon
    <1>5. ASSUME NEW q \in DOMAIN steps, q # r
          PROVE  steps'[q] = steps[q]
        BY <1>5, Zenon DEF Set
    <1>6. ASSUME NEW q \in DOMAIN steps'
          PROVE  HandledEv(steps'[q].ev)
        <2>1. CASE q = r
            <3>1. steps'[q].ev = ev
                BY ONLY <1>4, <2>1, Z3
            <3>2. HandledEv(ev)
                BY Zenon
            <3>3. QED
                BY ONLY <3>1, <3>2, Z3
        <2>2. CASE q # r
            <3>1. q \in DOMAIN steps /\ steps'[q] = steps[q]
                BY <1>2, <1>6, <2>2, Zenon DEF Set
            <3>2. steps'[q].ev = steps[q].ev
                BY ONLY <3>1, Z3
            <3>3. Typed
                BY Zenon
            <3>4. HandledEv(steps[q].ev)
                BY ONLY <3>1, <3>3, Z3 DEF Typed
            <3>5. QED
                BY ONLY <3>2, <3>4, Z3
        <2>3. QED
            BY <2>1, <2>2, Zenon
    <1>7. QED
        BY <1>6, Zenon DEF Typed

LEMMA ExtTyped ==
    ASSUME Typed,
           NEW ev \in ExternalEvent,
           SubmitExternal(ev),
           Origin /= {}
    PROVE  Typed'
PROOF
    <1>2. Origin /= {}
        BY Z3
    <1>3. ev \in Event
        BY Z3 DEF Event
    <1>4. HandledEv(ev)
        BY <1>2, <1>3, KnownEv, Z3
    <1>5. PICK r \in Rid \ DOMAIN steps : steps' = Set(steps, r, Fresh(ev))
        BY Zenon DEF SubmitExternal
    <1>6. r \notin DOMAIN steps
        BY <1>5, Zenon
    <1>7. Typed /\ HandledEv(ev) /\ r \notin DOMAIN steps
          /\ steps' = Set(steps, r, Fresh(ev))
        BY <1>4, <1>5, <1>6, Zenon
    <1>8. QED
        BY ONLY <1>7, AddTyped, Zenon

LEMMA IntTyped ==
    ASSUME Typed,
           NEW e,
           e.id \in Id,
           e.kind \in DeadlineKind,
           "Timeout" \in Implemented,
           Origin /= {},
           \E r \in Rid \ DOMAIN steps :
                steps' = Set(steps, r,
                             Fresh([tag |-> "Timeout", id |-> e.id,
                                    kind |-> e.kind]))
    PROVE  Typed'
PROOF
    <1> DEFINE nev == [tag |-> "Timeout", id |-> e.id, kind |-> e.kind]
    <1>1. "Timeout" \in Implemented /\ Origin /= {}
        BY Z3
    <1>2. e.id \in Id /\ e.kind \in DeadlineKind
        BY Z3
    <1>3. nev \in Event /\ nev.tag = "Timeout" /\ nev.id = e.id
        BY <1>1, <1>2, TimeoutIn, Z3 DEF nev
    <1>4. HandledEv(nev)
        BY <1>1, <1>3, KnownEv, Z3
    <1>5. PICK r \in Rid \ DOMAIN steps : steps' = Set(steps, r, Fresh(nev))
        BY Zenon DEF nev
    <1>6. r \notin DOMAIN steps
        BY <1>5, Zenon
    <1>7. Typed /\ HandledEv(nev) /\ r \notin DOMAIN steps
          /\ steps' = Set(steps, r, Fresh(nev))
        BY <1>4, <1>5, <1>6, Zenon
    <1>8. QED
        BY ONLY <1>7, AddTyped, Zenon

LEMMA ProcTyped ==
    ASSUME Typed, Shaped, NEW r \in DOMAIN steps, Process(r)
    PROVE  Typed'
PROOF
    <1> DEFINE o == OriginOf(steps[r].ev)
               swept == Sweep(docs[o], now)
               out == Handle(steps[r].ev, swept.doc, now)
               final == out.doc
               puts == swept.puts \o out.puts
               dels == swept.dels \o out.dels
               sends == swept.sends \o out.sends
               pre == [n \in 1 .. Len(puts) |->
                          [tag |-> "PutTimeout", entry |-> puts[n]]]
               rec == [tag |-> "PutDocument", body |-> final, sends |-> sends]
               post == [n \in 1 .. Len(dels) |->
                           [tag |-> "DelTimeout", entry |-> dels[n]]]
               seq == (pre \o <<rec>>) \o post
    <1>1. steps' = [steps EXCEPT ![r].phase   = "perform",
                                ![r].at      = now,
                                ![r].pending = seq,
                                ![r].expect  = docs[o]]
        BY Isa DEF Process, o, swept, out, final, puts, dels, sends,
                            pre, rec, post, seq
    <1>2. ASSUME NEW rr \in DOMAIN steps, NEW aa, NEW bb, NEW cc, NEW dd,
                 /\ rr = r
                 /\ aa = "perform"
                 /\ bb = now
                 /\ cc = seq
                 /\ dd = docs[o]
                 /\ Typed
                 /\ Shaped
                 /\ steps' = [steps EXCEPT ![rr].phase = aa, ![rr].at = bb,
                                            ![rr].pending = cc, ![rr].expect = dd]
          PROVE  Typed'
        BY <1>2, FourTyped, Isa
    <1>3. QED
        BY <1>1, <1>2, Zenon DEF o, seq

LEMMA TypeNext ==
    ASSUME Typed, Shaped, [Next]_vars,
           Origin /= {},
           "Timeout" \in Implemented,
           \A e \in timeouts : e.id \in Id /\ e.kind \in DeadlineKind
    PROVE  Typed'
PROOF
    <1>1. ASSUME UNCHANGED vars
          PROVE  Typed'
        <2>1. steps' = steps
            BY <1>1, Z3 DEF vars
        <2>2. QED
            BY <2>1, StayTyped, Isa
    <1>2. ASSUME NEW ev \in ExternalEvent, SubmitExternal(ev)
          PROVE  Typed'
        BY <1>2, ExtTyped, Isa
    <1>3. ASSUME NEW e \in timeouts, SubmitInternal(e)
          PROVE  Typed'
        <2>1. e.id \in Id /\ e.kind \in DeadlineKind
            BY <1>3, Z3
        <2>2. \E r \in Rid \ DOMAIN steps :
                  steps' = Set(steps, r,
                               Fresh([tag |-> "Timeout", id |-> e.id,
                                      kind |-> e.kind]))
            BY <1>3, Zenon DEF SubmitInternal
        <2>3. QED
            BY <1>3, <2>1, <2>2, IntTyped, Zenon
    <1>4. ASSUME NEW r \in DOMAIN steps, Process(r)
          PROVE  Typed'
        BY <1>4, ProcTyped, Isa
    <1>5. ASSUME NEW r \in DOMAIN steps, PerformDone(r)
          PROVE  Typed'
        <2>1. steps' = Del(steps, r)
            BY <1>5, Z3 DEF PerformDone
        <2>2. QED
            BY <1>5, <2>1, DelTyped, Zenon
    <1>6. ASSUME NEW r \in DOMAIN steps, Crash(r)
          PROVE  Typed'
        <2>1. steps' = Del(steps, r)
            BY <1>6, Z3 DEF Crash
        <2>2. QED
            BY <1>6, <2>1, DelTyped, Zenon
    <1>7. ASSUME Clock
          PROVE  Typed'
        <2>1. steps' = steps
            BY <1>7, Z3 DEF Clock
        <2>2. QED
            BY <2>1, StayTyped, Isa
    <1>8. ASSUME NEW r \in DOMAIN steps, PerformPutTimeout(r)
          PROVE  Typed'
        <2>1. steps' = [steps EXCEPT ![r].pending = Tail(steps[r].pending)]
            BY <1>8, Isa DEF PerformPutTimeout
        <2>2. ASSUME NEW rr \in DOMAIN steps, NEW ee,
                     /\ rr = r
                     /\ ee = Tail(steps[r].pending)
                     /\ Typed
                     /\ Shaped
                     /\ steps' = [steps EXCEPT ![rr].pending = ee]
              PROVE  Typed'
            BY <2>2, OneTyped, Zenon
        <2>3. QED
            BY <1>8, <2>1, <2>2, Zenon
    <1>9. ASSUME NEW r \in DOMAIN steps, PerformPut(r)
          PROVE  Typed'
        <2>1. steps' = [steps EXCEPT ![r].pending = Tail(steps[r].pending)]
            BY <1>9, Isa DEF PerformPut
        <2>2. ASSUME NEW rr \in DOMAIN steps, NEW ee,
                     /\ rr = r
                     /\ ee = Tail(steps[r].pending)
                     /\ Typed
                     /\ Shaped
                     /\ steps' = [steps EXCEPT ![rr].pending = ee]
              PROVE  Typed'
            BY <2>2, OneTyped, Zenon
        <2>3. QED
            BY <1>9, <2>1, <2>2, Zenon
    <1>10. ASSUME NEW r \in DOMAIN steps, PerformDelTimeout(r)
           PROVE  Typed'
        <2>1. steps' = [steps EXCEPT ![r].pending = Tail(steps[r].pending)]
            BY <1>10, Isa DEF PerformDelTimeout
        <2>2. ASSUME NEW rr \in DOMAIN steps, NEW ee,
                     /\ rr = r
                     /\ ee = Tail(steps[r].pending)
                     /\ Typed
                     /\ Shaped
                     /\ steps' = [steps EXCEPT ![rr].pending = ee]
              PROVE  Typed'
            BY <2>2, OneTyped, Zenon
        <2>3. QED
            BY <1>10, <2>1, <2>2, Zenon
    <1>11. ASSUME NEW r \in DOMAIN steps, PerformMiss(r)
           PROVE  Typed'
        <2>1. steps' = [steps EXCEPT ![r].phase = "process",
                                     ![r].pending = << >>]
            BY <1>11, Isa DEF PerformMiss
        <2>2. ASSUME NEW rr \in DOMAIN steps,
                     /\ rr = r
                     /\ Typed
                     /\ Shaped
                     /\ steps' = [steps EXCEPT ![rr].phase = "process",
                                              ![rr].pending = << >>]
              PROVE  Typed'
            BY <2>2, MissTyped, Zenon
        <2>3. QED
            BY <1>11, <2>1, <2>2, Zenon
    <1>12. QED
        <2>1. CASE UNCHANGED vars
            BY <2>1, <1>1, Z3
        <2>2. CASE \E ev \in ExternalEvent : SubmitExternal(ev)
            <3>1. PICK ev \in ExternalEvent : SubmitExternal(ev)
                BY <2>2, Z3
            <3>2. QED
                BY <3>1, <1>2, Z3
        <2>3. CASE \E e \in timeouts : SubmitInternal(e)
            <3>1. PICK e \in timeouts : SubmitInternal(e)
                BY <2>3, Z3
            <3>2. QED
                BY <3>1, <1>3, Z3
        <2>4. CASE \E r \in DOMAIN steps : Process(r)
            <3>1. PICK r \in DOMAIN steps : Process(r)
                BY <2>4, Z3
            <3>2. QED
                BY <3>1, <1>4, Z3
        <2>5. CASE \E r \in DOMAIN steps : Crash(r)
            <3>1. PICK r \in DOMAIN steps : Crash(r)
                BY <2>5, Z3
            <3>2. QED
                BY <3>1, <1>6, Z3
        <2>6. CASE Clock
            BY <2>6, <1>7, Z3
        <2>7. CASE \E r \in DOMAIN steps : Perform(r)
            <3>1. PICK r \in DOMAIN steps : Perform(r)
                BY <2>7, Z3
            <3>2. CASE PerformDone(r)
                BY <3>1, <3>2, <1>5, Z3 DEF Perform
            <3>3. CASE PerformPutTimeout(r)
                BY <3>1, <3>3, <1>8, Z3 DEF Perform
            <3>4. CASE PerformDelTimeout(r)
                BY <3>1, <3>4, <1>10, Z3 DEF Perform
            <3>5. CASE PerformMiss(r)
                BY <3>1, <3>5, <1>11, Z3 DEF Perform
            <3>6. CASE PerformPut(r)
                BY <3>1, <3>6, <1>9, Z3 DEF Perform
            <3>7. QED
                BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, Z3 DEF Perform
        <2>8. QED
            BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, Z3 DEF Next, vars

LEMMA PlaceHold ==
    ASSUME Placed, Queued, Typed, Shaped, [Next]_vars,
           Origin /= {},
           "Timeout" \in Implemented,
           \A e \in timeouts : e.id \in Id /\ e.kind \in DeadlineKind
    PROVE  Placed' /\ Queued' /\ Shaped' /\ Typed'
PROOF
    <1>1. Placed'
        BY PlaceNext, Z3
    <1>2. Queued' /\ Shaped'
        BY InvStep, Z3
    <1>3. Typed'
        BY TypeNext, Z3
    <1>4. QED
        BY <1>1, <1>2, <1>3, Z3

THEOREM PlaceAlways ==
    ASSUME Origin /= {},
           "Timeout" \in Implemented
    PROVE  Init /\ [][Next]_vars
            /\ [](\A e \in timeouts : e.id \in Id /\ e.kind \in DeadlineKind)
            => [](Placed /\ Queued /\ Shaped /\ Typed)
PROOF
    <1>1. Init => Placed /\ Queued /\ Shaped /\ Typed
        <2>1. ASSUME Init
              PROVE  Placed /\ Queued /\ Shaped /\ Typed
            <3>1. Placed
                BY <2>1, PlacedInit, Z3
            <3>2. Queued /\ Shaped
                BY <2>1, InvInit, Z3
            <3>3. Typed
                BY <2>1, TypeInit, Z3
            <3>4. QED
                BY <3>1, <3>2, <3>3, Z3
        <2>2. QED
            BY <2>1, Z3
    <1>2. ASSUME Placed /\ Queued /\ Shaped /\ Typed,
                 \A e \in timeouts : e.id \in Id /\ e.kind \in DeadlineKind,
                 [Next]_vars
          PROVE  Placed' /\ Queued' /\ Shaped' /\ Typed'
        BY <1>2, PlaceHold, Z3
    <1>3. QED
        BY <1>1, <1>2, PTL

=============================================================================
