------------------------------- MODULE Proof -------------------------------
(* The executor and the protocol start together. A concrete step that does
   not land a document is a protocol step, or it leaves the protocol's
   variables where they are. Landing the document is a sweep at the recorded
   decision time and then the handler. *)
EXTENDS PerformNext, SequenceTheorems, NaturalsInduction, TLAPS

ASSUME OriginNamed == Origin /= {}
ASSUME TimeoutOn == "Timeout" \in Implemented

ASSUME DeadlineStepA ==
    DeadlineOk /\ [Next]_vars => DeadlineOk'

AbsVars ==
    <<Objects, outbox, now>>

AbsStep ==
    P!Next \/ UNCHANGED AbsVars

(* The initial states coincide: an empty document is an empty store, and both
   clocks start at 0. *)
THEOREM InitImplies ==
    ASSUME Init
    PROVE  P!Init
PROOF
    <1>1. EmptyFn = << >> /\ P!EmptyFn = << >>
        BY DEF EmptyFn, P!EmptyFn
    <1>2. << >> \in Seq(Nat) /\ Len(<< >>) = 0
        BY EmptySeq
    <1>3. DOMAIN << >> = {}
        BY <1>2, LenProperties
    <1>4. docs = [o \in Origin |-> EmptyFn] /\ outbox = {} /\ now = 0
        BY DEF Init
    <1>5. ASSUME NEW o \in Origin
          PROVE  docs[o] = << >>
        BY <1>1, <1>4
    <1>6. \A o \in Origin : DOMAIN docs[o] = {}
        BY <1>3, <1>5
    <1>7. UNION { DOMAIN docs[o] : o \in Origin } = {}
        BY <1>6
    <1>8. Objects = [i \in {} |-> docs[i.origin][i]]
        BY <1>7 DEF Objects
    <1>9. Objects = << >>
        BY <1>1, <1>3, <1>8
    <1>10. QED
        BY <1>1, <1>4, <1>9 DEF P!Init

(* A successful document write leaves the clock where it is. So does every
   other arm of a perform. *)
LEMMA WriteLeavesClock ==
    ASSUME NEW r \in DOMAIN steps, Perform(r)
    PROVE  now' = now
PROOF
    <1>1. CASE PerformDone(r)
        BY <1>1 DEF PerformDone
    <1>2. CASE PerformPutTimeout(r)
        BY <1>2 DEF PerformPutTimeout
    <1>3. CASE PerformPut(r)
        BY <1>3 DEF PerformPut
    <1>4. CASE PerformMiss(r)
        BY <1>4 DEF PerformMiss
    <1>5. CASE PerformDelTimeout(r)
        BY <1>5 DEF PerformDelTimeout
    <1>6. QED
        BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Perform

(* A step that does not land a document is a protocol step, or it does not
   touch the store the protocol can see. *)
THEOREM QuietStep ==
    ASSUME Next,
           \A r \in DOMAIN steps : ~PerformPut(r)
    PROVE  P!Next \/ UNCHANGED <<Objects, outbox, now>>
PROOF
    <1>1. ASSUME NEW ev \in ExternalEvent, SubmitExternal(ev)
          PROVE  UNCHANGED <<Objects, outbox, now>>
        BY <1>1 DEF SubmitExternal, Objects
    <1>2. ASSUME NEW name \in DOMAIN timeouts, SubmitInternal(name)
          PROVE  UNCHANGED <<Objects, outbox, now>>
        BY <1>2 DEF SubmitInternal, Objects
    <1>3. ASSUME NEW r \in DOMAIN steps, Process(r)
          PROVE  UNCHANGED <<Objects, outbox, now>>
        BY <1>3 DEF Process, Objects
    <1>4. ASSUME NEW r \in DOMAIN steps, Crash(r)
          PROVE  UNCHANGED <<Objects, outbox, now>>
        BY <1>4 DEF Crash, Objects
    <1>5. ASSUME Clock
          PROVE  P!Next
        <2>1. UNCHANGED Objects
            BY <1>5 DEF Clock, Objects
        <2>2. P!Clock
            BY <1>5, <2>1 DEF Clock, P!Clock
        <2>3. QED
            BY <2>2 DEF P!Next
    <1>6. ASSUME NEW r \in DOMAIN steps, PerformDone(r)
          PROVE  UNCHANGED <<Objects, outbox, now>>
        BY <1>6 DEF PerformDone, Objects
    <1>7. ASSUME NEW r \in DOMAIN steps, PerformPutTimeout(r)
          PROVE  UNCHANGED <<Objects, outbox, now>>
        BY <1>7 DEF PerformPutTimeout, Objects
    <1>8. ASSUME NEW r \in DOMAIN steps, PerformDelTimeout(r)
          PROVE  UNCHANGED <<Objects, outbox, now>>
        BY <1>8 DEF PerformDelTimeout, Objects
    <1>9. ASSUME NEW r \in DOMAIN steps, PerformMiss(r)
          PROVE  UNCHANGED <<Objects, outbox, now>>
        BY <1>9 DEF PerformMiss, Objects
    <1>10. ASSUME NEW r \in DOMAIN steps, PerformPut(r)
           PROVE  P!Next \/ UNCHANGED <<Objects, outbox, now>>
        BY <1>10, Z3
    <1>11. QED
        <2>1. CASE \E ev \in ExternalEvent : SubmitExternal(ev)
            <3>1. PICK ev \in ExternalEvent : SubmitExternal(ev)
                BY <2>1
            <3>2. QED
                BY <3>1, <1>1
        <2>2. CASE \E name \in DOMAIN timeouts : SubmitInternal(name)
            <3>1. PICK name \in DOMAIN timeouts : SubmitInternal(name)
                BY <2>2
            <3>2. QED
                BY <3>1, <1>2
        <2>3. CASE \E r \in DOMAIN steps : Process(r)
            <3>1. PICK r \in DOMAIN steps : Process(r)
                BY <2>3
            <3>2. QED
                BY <3>1, <1>3
        <2>4. CASE \E r \in DOMAIN steps : Crash(r)
            <3>1. PICK r \in DOMAIN steps : Crash(r)
                BY <2>4
            <3>2. QED
                BY <3>1, <1>4
        <2>5. CASE Clock
            BY <2>5, <1>5
        <2>6. CASE \E r \in DOMAIN steps : Perform(r)
            <3>1. PICK r \in DOMAIN steps : Perform(r)
                BY <2>6
            <3>2. CASE PerformDone(r)
                BY <3>1, <3>2, <1>6 DEF Perform
            <3>3. CASE PerformPutTimeout(r)
                BY <3>1, <3>3, <1>7 DEF Perform
            <3>4. CASE PerformDelTimeout(r)
                BY <3>1, <3>4, <1>8 DEF Perform
            <3>5. CASE PerformMiss(r)
                BY <3>1, <3>5, <1>9 DEF Perform
            <3>6. CASE PerformPut(r)
                BY <3>1, <3>6, <1>10 DEF Perform
            <3>7. QED
                BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Perform
        <2>7. QED
            BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next

LEMMA Stutter ==
    ASSUME UNCHANGED vars
    PROVE  UNCHANGED <<Objects, outbox, now>>
PROOF
    BY DEF vars, Objects

LEMMA AbstractStep ==
    ASSUME Placed, Queued, Typed, [Next]_vars
    PROVE  AbsStep
PROOF
    <1>1. CASE UNCHANGED vars
        <2>1. UNCHANGED <<Objects, outbox, now>>
            BY <1>1, Stutter
        <2>2. QED
            BY <2>1 DEF AbsStep, AbsVars
    <1>2. CASE Next
        <2>1. CASE \A r \in DOMAIN steps : ~PerformPut(r)
            <3>1. P!Next \/ UNCHANGED <<Objects, outbox, now>>
                BY <1>2, <2>1, QuietStep
            <3>2. QED
                BY <3>1 DEF AbsStep, AbsVars
        <2>2. CASE \E r \in DOMAIN steps : PerformPut(r)
            <3>1. PICK r \in DOMAIN steps : PerformPut(r)
                BY <2>2
            <3>2. P!Next \/ UNCHANGED <<Objects, outbox, now>>
                BY <3>1, PerformPutStep
            <3>3. QED
                BY <3>2 DEF AbsStep, AbsVars
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2 DEF vars

LEMMA DeadlineInit ==
    ASSUME Init
    PROVE  DeadlineOk
PROOF
    <1>1. timeouts = EmptyFn /\ EmptyFn = << >>
        BY DEF Init, EmptyFn
    <1>2. << >> \in Seq(Nat) /\ Len(<< >>) = 0
        BY EmptySeq
    <1>3. DOMAIN << >> = {}
        BY <1>2, LenProperties
    <1>4. DOMAIN timeouts = {}
        BY <1>1, <1>3, Z3
    <1>5. QED
        BY <1>4 DEF DeadlineOk

THEOREM DeadlineAlways ==
    ConcreteBehavior => []DeadlineOk
PROOF
    <1>1. Init => DeadlineOk
        BY DeadlineInit
    <1>2. DeadlineOk /\ [Next]_vars => DeadlineOk'
        BY DeadlineStepA
    <1>3. QED
        BY <1>1, <1>2, PTL DEF ConcreteBehavior

THEOREM InvariantsAlways ==
    ConcreteBehavior => [](Placed /\ Queued /\ Shaped /\ Typed)
PROOF
    <1>1. ConcreteBehavior => []DeadlineOk
        BY DeadlineAlways
    <1>2. Init /\ [][Next]_vars /\ []DeadlineOk
          => [](Placed /\ Queued /\ Shaped /\ Typed)
        BY PlaceAlways, OriginNamed, TimeoutOn, PTL DEF DeadlineOk
    <1>3. QED
        BY <1>1, <1>2, PTL DEF ConcreteBehavior

THEOREM AbstractStepsAlways ==
    ConcreteBehavior => []AbsStep
PROOF
    <1>1. Placed /\ Queued /\ Shaped /\ Typed /\ [Next]_vars => AbsStep
        BY AbstractStep, Z3
    <1>2. ConcreteBehavior => [](Placed /\ Queued /\ Shaped /\ Typed)
        BY InvariantsAlways
    <1>3. QED
        BY <1>1, <1>2, PTL DEF ConcreteBehavior

THEOREM ConcreteRefinesAbstract ==
    Init /\ [][Next]_vars => P!Safety
PROOF
    <1>1. ConcreteBehavior => P!Init
        BY InitImplies DEF ConcreteBehavior
    <1>2. ConcreteBehavior => []AbsStep
        BY AbstractStepsAlways
    <1>3. P!vars = AbsVars
        BY DEF P!vars, AbsVars
    <1>4a. UNCHANGED AbsVars <=> UNCHANGED P!vars
        BY ONLY DEF AbsVars, P!vars
    <1>4. AbsStep <=> (P!Next \/ UNCHANGED P!vars)
        BY ONLY <1>4a, Z3 DEF AbsStep
    <1>5. ConcreteBehavior => [](P!Next \/ UNCHANGED P!vars)
        BY <1>2, <1>4, PTL
    <1>6. ConcreteBehavior => [][P!Next]_P!vars
        BY <1>5
    <1>7. QED
        BY <1>1, <1>6, PTL DEF ConcreteBehavior, P!Safety

===============================================================================
