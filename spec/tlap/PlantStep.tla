------------------------------ MODULE PlantStep ------------------------------
(* The handler runs on the swept document and the write plants that result.
   A second origin-local plant replaces the first, and writing one id in the
   origin document is writing that id in the whole store. *)
EXTENDS Plant

LEMMA PlantTwice ==
    ASSUME NEW base, NEW o, NEW mid, NEW body,
           \A i \in DOMAIN mid : i.origin = o,
           \A i \in DOMAIN body : i.origin = o
    PROVE  Plant(Plant(base, o, mid), o, body) = Plant(base, o, body)
PROOF
    <1> DEFINE inner == Plant(base, o, mid)
    <1> DEFINE kept == { j \in DOMAIN base : j.origin /= o }
    <1> DEFINE keptI == { j \in DOMAIN inner : j.origin /= o }
    <1> DEFINE dom == kept \cup DOMAIN body
    <1> DEFINE domI == keptI \cup DOMAIN body
    <1>1. DOMAIN inner = kept \cup DOMAIN mid
        BY DEF inner, Plant, kept
    <1>2. keptI = kept
        <2>1. keptI \subseteq kept
            <3> SUFFICES ASSUME NEW k \in keptI
                         PROVE  k \in kept
                OBVIOUS
            <3>1. k \in DOMAIN inner /\ k.origin /= o
                BY DEF keptI
            <3>2. k \in kept \/ k \in DOMAIN mid
                BY <1>1, <3>1
            <3>3. k \notin DOMAIN mid
                BY <3>1
            <3>4. QED
                BY <3>2, <3>3 DEF kept
        <2>2. kept \subseteq keptI
            <3> SUFFICES ASSUME NEW k \in kept
                         PROVE  k \in keptI
                OBVIOUS
            <3>1. k \in DOMAIN base /\ k.origin /= o
                BY DEF kept
            <3>2. k \in DOMAIN inner
                BY <1>1, <3>1
            <3>3. QED
                BY <3>1, <3>2 DEF keptI
        <2>3. QED
            BY <2>1, <2>2
    <1>3. domI = dom
        BY <1>2 DEF domI, dom
    <1>4. \A i \in DOMAIN inner :
            inner[i] = IF i \in DOMAIN mid THEN mid[i] ELSE base[i]
        BY DEF inner, Plant, kept
    <1>5. \A i \in dom :
            (IF i \in DOMAIN body THEN body[i] ELSE base[i])
              = (IF i \in DOMAIN body THEN body[i]
                 ELSE IF i \in DOMAIN mid THEN mid[i] ELSE base[i])
        <2> SUFFICES ASSUME NEW k \in dom
                     PROVE  (IF k \in DOMAIN body THEN body[k] ELSE base[k])
                               = (IF k \in DOMAIN body THEN body[k]
                                  ELSE IF k \in DOMAIN mid THEN mid[k] ELSE base[k])
            OBVIOUS
        <2>1. CASE k \in DOMAIN body
            BY <2>1
        <2>2. CASE k \notin DOMAIN body
            <3>1. k \in kept
                BY <2>2 DEF dom
            <3>2. k.origin /= o
                BY <3>1 DEF kept
            <3>3. k \notin DOMAIN mid
                BY <3>2
            <3>4. QED
                BY <2>2, <3>3
        <2>3. QED
            BY <2>1, <2>2
    <1>6. Plant(inner, o, body)
            = [ i \in domI |-> IF i \in DOMAIN body THEN body[i] ELSE inner[i] ]
        BY DEF Plant, keptI, domI
    <1>7. \A i \in domI :
            (IF i \in DOMAIN body THEN body[i] ELSE inner[i])
              = (IF i \in DOMAIN body THEN body[i] ELSE base[i])
        <2> SUFFICES ASSUME NEW k \in domI
                     PROVE  (IF k \in DOMAIN body THEN body[k] ELSE inner[k])
                               = (IF k \in DOMAIN body THEN body[k] ELSE base[k])
            OBVIOUS
        <2>1. CASE k \in DOMAIN body
            BY <2>1
        <2>2. CASE k \notin DOMAIN body
            <3>1. k \in keptI
                BY <2>2 DEF domI
            <3>2. k \in kept /\ k \in DOMAIN inner /\ k.origin /= o
                BY <1>2, <3>1 DEF keptI
            <3>3. k \notin DOMAIN mid
                BY <3>2
            <3>4. inner[k] = base[k]
                BY <1>4, <3>2, <3>3
            <3>5. QED
                BY <2>2, <3>4
        <2>3. QED
            BY <2>1, <2>2
    <1>8. Plant(base, o, body)
            = [ i \in dom |-> IF i \in DOMAIN body THEN body[i] ELSE base[i] ]
        BY DEF Plant, kept, dom
    <1>9. [ i \in domI |-> IF i \in DOMAIN body THEN body[i] ELSE inner[i] ]
            = [ i \in dom |-> IF i \in DOMAIN body THEN body[i] ELSE base[i] ]
        BY <1>3, <1>7, ExtCtor
    <1>10. QED
        BY <1>6, <1>8, <1>9 DEF inner

LEMMA PlantWrite ==
    ASSUME NEW base, NEW o, NEW doc, NEW id, NEW obj,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  Plant(base, o, Write(doc, id, obj)) = Write(base, id, obj)
PROOF
    <1> DEFINE body == Write(doc, id, obj)
    <1> DEFINE kept == { j \in DOMAIN base : j.origin /= o }
    <1> DEFINE domP == kept \cup DOMAIN body
    <1> DEFINE domW == (DOMAIN base) \cup {id}
    <1>1. DOMAIN body = (DOMAIN doc) \cup {id}
        BY DEF body, Write
    <1>2. \A i \in DOMAIN body : i.origin = o
        <2> SUFFICES ASSUME NEW k \in DOMAIN body
                     PROVE  k.origin = o
            OBVIOUS
        <2>1. k \in DOMAIN doc \/ k = id
            BY <1>1
        <2>2. CASE k \in DOMAIN doc
            BY <2>2
        <2>3. CASE k = id
            BY <2>3
        <2>4. QED
            BY <2>1, <2>2, <2>3
    <1>3. domP = domW
        <2>1. domP \subseteq domW
            <3> SUFFICES ASSUME NEW k \in domP
                         PROVE  k \in domW
                OBVIOUS
            <3>1. CASE k \in kept
                BY <3>1 DEF kept, domW
            <3>2. CASE k \in DOMAIN body
                <4>1. k \in DOMAIN doc \/ k = id
                    BY <1>1, <3>2
                <4>2. QED
                    BY <4>1 DEF domW
            <3>3. QED
                BY <3>1, <3>2 DEF domP
        <2>2. domW \subseteq domP
            <3> SUFFICES ASSUME NEW k \in domW
                         PROVE  k \in domP
                OBVIOUS
            <3>1. CASE k = id
                BY <1>1, <3>1 DEF domP
            <3>2. CASE k \in DOMAIN base /\ k /= id
                <4>1. CASE k.origin = o
                    <5>1. k \in DOMAIN doc
                        BY <4>1, <3>2
                    <5>2. QED
                        BY <1>1, <5>1 DEF domP
                <4>2. CASE k.origin /= o
                    BY <3>2, <4>2 DEF kept, domP
                <4>3. QED
                    BY <4>1, <4>2
            <3>3. QED
                BY <3>1, <3>2 DEF domW
        <2>3. QED
            BY <2>1, <2>2
    <1>4. \A i \in DOMAIN body :
            body[i] = IF i = id THEN obj ELSE doc[i]
        BY DEF body, Write
    <1>5. \A i \in domP :
            (IF i \in DOMAIN body THEN body[i] ELSE base[i])
              = (IF i = id THEN obj ELSE base[i])
        <2> SUFFICES ASSUME NEW k \in domP
                     PROVE  (IF k \in DOMAIN body THEN body[k] ELSE base[k])
                               = (IF k = id THEN obj ELSE base[k])
            OBVIOUS
        <2>1. CASE k = id
            <3>1. k \in DOMAIN body
                BY <1>1, <2>1
            <3>2. body[k] = obj
                BY <1>4, <2>1, <3>1
            <3>3. QED
                BY <2>1, <3>1, <3>2
        <2>2. CASE k /= id /\ k \in DOMAIN body
            <3>1. k \in DOMAIN doc
                BY <1>1, <2>2
            <3>2. body[k] = doc[k]
                BY <1>4, <2>2
            <3>3. doc[k] = base[k]
                BY <3>1
            <3>4. QED
                BY <2>2, <3>2, <3>3
        <2>3. CASE k /= id /\ k \notin DOMAIN body
            BY <2>3
        <2>4. QED
            BY <2>1, <2>2, <2>3
    <1>6. Plant(base, o, body)
            = [ i \in domP |-> IF i \in DOMAIN body THEN body[i] ELSE base[i] ]
        BY DEF Plant, kept, domP
    <1>7. Write(base, id, obj)
            = [ i \in domW |-> IF i = id THEN obj ELSE base[i] ]
        BY DEF Write, domW
    <1>8. [ i \in domP |-> IF i \in DOMAIN body THEN body[i] ELSE base[i] ]
            = [ i \in domW |-> IF i = id THEN obj ELSE base[i] ]
        BY <1>3, <1>5, ExtCtor
    <1>9. QED
        BY <1>6, <1>7, <1>8 DEF body

(* An enabled settle on the origin document, planted into the store, is the
   store the abstract settle returns. A disabled settle leaves the document. *)
LEMMA SettleLift ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  LET c == HandlePromiseSettle(req, doc, t)
                a == P!HandlePromiseSettle(base, req, t)
            IN  IF a = {} THEN c.doc = doc
                ELSE a = {Plant(base, o, c.doc)}
PROOF
    <1> DEFINE c == HandlePromiseSettle(req, doc, t)
    <1> DEFINE a == P!HandlePromiseSettle(base, req, t)
    <1> DEFINE id == req.id
    <1>1. CASE id \notin DOMAIN doc
        <2>1. id \notin DOMAIN base
            BY <1>1, Zenon DEF id
        <2>2. c = Skip(doc) /\ a = {}
            BY <1>1, <2>1 DEF c, a, id, HandlePromiseSettle, P!HandlePromiseSettle
        <2>3. QED
            BY <2>2 DEF Skip
    <1>2. CASE id \in DOMAIN doc
        <2>1. id \in DOMAIN base /\ base[id] = doc[id] /\ id.origin = o
            BY <1>2, Zenon DEF id
        <2>2. Project(doc[id], t) = P!Project(base[id], t)
            BY <2>1, Isa DEF Project, P!Project, NoTime, P!NoTime, NoTask, P!NoTask
        <2> DEFINE old == Project(doc[id], t)
        <2>3. CASE old.promise.state /= "pending"
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2, <2>3 DEF c, a, old, id,
                   HandlePromiseSettle, P!HandlePromiseSettle
            <3>2. QED
                BY <3>1 DEF Skip
        <2>4. CASE old.promise.state = "pending"
            <3> DEFINE new ==
                    [ promise |-> [old.promise EXCEPT !.state     = req.state,
                                                     !.value     = req.value,
                                                     !.settledAt = t],
                      task    |-> [old.task EXCEPT !.state          = IF @ = "none" THEN "none"
                                                                      ELSE "fulfilled",
                                                   !.pid            = NoPid,
                                                   !.ttl            = NoTime,
                                                   !.leaseTimeoutAt = NoTime,
                                                   !.retryTimeoutAt = NoTime,
                                                   !.resumes        = {}] ]
            <3> DEFINE oldA == P!Project(base[id], t)
            <3> DEFINE newA ==
                    [ promise |-> [oldA.promise EXCEPT !.state     = req.state,
                                                       !.value     = req.value,
                                                       !.settledAt = t],
                      task    |-> [oldA.task EXCEPT !.state          = IF @ = "none" THEN "none"
                                                                      ELSE "fulfilled",
                                                   !.pid            = NoPid,
                                                   !.ttl            = P!NoTime,
                                                   !.leaseTimeoutAt = P!NoTime,
                                                   !.retryTimeoutAt = P!NoTime,
                                                   !.resumes        = {}] ]
            <3>1. NoTime = P!NoTime
                BY DEF NoTime, P!NoTime
            <3>2. oldA = old /\ newA = new
                BY <2>2, <3>1, Isa DEF old, oldA, new, newA, NoTime, P!NoTime
            <3>3. c.doc = Write(doc, id, new)
                BY <1>2, <2>4, Isa DEF c, old, new, id, HandlePromiseSettle, Skip
            <3>4. a = {P!Write(base, id, newA)}
                BY <2>1, <2>4, <3>2, Isa DEF a, old, oldA, newA, id, P!HandlePromiseSettle
            <3>5. Plant(base, o, Write(doc, id, new)) = Write(base, id, new)
                <4>1. ASSUME NEW ii, NEW nw,
                             ii = id, nw = new, ii.origin = o
                      PROVE  Plant(base, o, Write(doc, ii, nw)) = Write(base, ii, nw)
                    BY <4>1, PlantWrite
                <4>2. QED
                    BY <2>1, <4>1, Zenon DEF id
            <3>6. Write(base, id, new) = P!Write(base, id, new)
                <4>1. ASSUME NEW ii, NEW nw,
                             ii = id, nw = new
                      PROVE  Write(base, ii, nw) = P!Write(base, ii, nw)
                    BY <4>1 DEF Write, P!Write
                <4>2. QED
                    BY <4>1, Zenon DEF id
            <3>7. Write(base, id, new) = P!Write(base, id, newA)
                BY <3>2, <3>6, Zenon, Isa DEF P!Write
            <3>8. a = {Plant(base, o, c.doc)}
                BY <3>3, <3>4, <3>5, <3>7
            <3>9. QED
                BY <3>8
        <2>5. QED
            BY <2>3, <2>4
    <1>3. QED
        BY <1>1, <1>2 DEF c, a

(* A create on the origin document, planted into the store, is the store the
   abstract create returns. An id that is already there leaves the document. *)
LEMMA CreateLift ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  LET c == HandlePromiseCreate(req, doc, t)
                a == P!HandlePromiseCreate(base, req, t)
            IN  IF a = {} THEN c.doc = doc
                ELSE a = {Plant(base, o, c.doc)}
PROOF
    <1> DEFINE c == HandlePromiseCreate(req, doc, t)
    <1> DEFINE a == P!HandlePromiseCreate(base, req, t)
    <1> DEFINE id == req.id
    <1>1. CASE id \in DOMAIN doc
        <2>1. id \in DOMAIN base
            BY <1>1, Zenon DEF id
        <2>2. c = Skip(doc) /\ a = {}
            BY <1>1, <2>1 DEF c, a, id, HandlePromiseCreate, P!HandlePromiseCreate
        <2>3. QED
            BY <2>2 DEF Skip
    <1>2. CASE id \notin DOMAIN doc
        <2>1. id \notin DOMAIN base /\ id.origin = o
            BY <1>2, Zenon DEF id
        <2>2. New(req, t) = P!New(req, t)
            BY Isa DEF New, P!New, NoTime, P!NoTime, NoTask, P!NoTask
        <2> DEFINE born == New(req, t)
        <2>3. c.doc = Write(doc, id, born)
            BY <1>2, Isa DEF c, born, id, HandlePromiseCreate, Skip
        <2>4. a = {P!Write(base, id, born)}
            BY <2>1, <2>2, Isa DEF a, born, id, P!HandlePromiseCreate, P!New
        <2>5. Plant(base, o, Write(doc, id, born)) = Write(base, id, born)
            <3>1. ASSUME NEW ii, NEW nw,
                         ii = id, nw = born, ii.origin = o
                  PROVE  Plant(base, o, Write(doc, ii, nw)) = Write(base, ii, nw)
                BY <3>1, PlantWrite
            <3>2. QED
                BY <2>1, <3>1, Zenon DEF id
        <2>6. Write(base, id, born) = P!Write(base, id, born)
            <3>1. ASSUME NEW ii, NEW nw,
                         ii = id, nw = born
                  PROVE  Write(base, ii, nw) = P!Write(base, ii, nw)
                BY <3>1 DEF Write, P!Write
            <3>2. QED
                BY <3>1, Zenon DEF id
        <2>7. a = {Plant(base, o, c.doc)}
            BY <2>3, <2>4, <2>5, <2>6
        <2>8. QED
            BY <2>7
    <1>3. QED
        BY <1>1, <1>2 DEF c, a

(* A listener on this origin's awaited id, planted into the store, is the
   store the abstract listener returns. *)
LEMMA ListenerLift ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.awaited.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  LET c == HandlePromiseRegisterListener(req, doc, t)
                a == P!HandlePromiseRegisterListener(base, req, t)
            IN  IF a = {} THEN c.doc = doc
                ELSE a = {Plant(base, o, c.doc)}
PROOF
    <1> DEFINE c == HandlePromiseRegisterListener(req, doc, t)
    <1> DEFINE a == P!HandlePromiseRegisterListener(base, req, t)
    <1> DEFINE id == req.awaited
    <1>1. CASE id \notin DOMAIN doc
        <2>1. id \notin DOMAIN base
            BY <1>1, Zenon DEF id
        <2>2. c = Skip(doc) /\ a = {}
            BY <1>1, <2>1 DEF c, a, id, HandlePromiseRegisterListener,
                   P!HandlePromiseRegisterListener
        <2>3. QED
            BY <2>2 DEF Skip
    <1>2. CASE id \in DOMAIN doc
        <2>1. id \in DOMAIN base /\ base[id] = doc[id] /\ id.origin = o
            BY <1>2, Zenon DEF id
        <2>2. Project(doc[id], t) = P!Project(base[id], t)
            BY <2>1, Isa DEF Project, P!Project, NoTime, P!NoTime, NoTask, P!NoTask
        <2> DEFINE old == Project(doc[id], t)
        <2>3. IsExternal(old.promise) <=> P!IsExternal(old.promise)
            BY DEF IsExternal, P!IsExternal, old
        <2>4. CASE ~IsExternal(old.promise)
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2, <2>3, <2>4 DEF c, a, old, id,
                       HandlePromiseRegisterListener, P!HandlePromiseRegisterListener
            <3>2. QED
                BY <3>1 DEF Skip
        <2>5. CASE old.promise.state /= "pending"
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2, <2>5 DEF c, a, old, id,
                       HandlePromiseRegisterListener, P!HandlePromiseRegisterListener
            <3>2. QED
                BY <3>1 DEF Skip
        <2>6. CASE IsExternal(old.promise) /\ old.promise.state = "pending"
            <3> DEFINE nw == [old EXCEPT !.promise.listeners = @ \cup {req.address}]
            <3>1. c.doc = Write(doc, id, nw)
                BY <1>2, <2>6 DEF c, old, nw, id, HandlePromiseRegisterListener
            <3>2. a = {P!Write(base, id, nw)}
                BY <2>1, <2>2, <2>3, <2>6, Isa DEF a, old, nw, id,
                       P!HandlePromiseRegisterListener, IsExternal, P!IsExternal
            <3>3. Plant(base, o, Write(doc, id, nw)) = Write(base, id, nw)
                <4>1. ASSUME NEW ii, NEW obj,
                             ii = id, obj = nw, ii.origin = o
                      PROVE  Plant(base, o, Write(doc, ii, obj)) = Write(base, ii, obj)
                    BY <4>1, PlantWrite
                <4>2. QED
                    BY <2>1, <4>1, Zenon DEF id
            <3>4. Write(base, id, nw) = P!Write(base, id, nw)
                <4>1. ASSUME NEW ii, NEW obj,
                             ii = id, obj = nw
                      PROVE  Write(base, ii, obj) = P!Write(base, ii, obj)
                    BY <4>1 DEF Write, P!Write
                <4>2. QED
                    BY <4>1, Zenon DEF id
            <3>5. a = {Plant(base, o, c.doc)}
                BY <3>1, <3>2, <3>3, <3>4
            <3>6. QED
                BY <3>5
        <2>7. QED
            BY <2>4, <2>5, <2>6
    <1>3. QED
        BY <1>1, <1>2 DEF c, a

(* A callback whose awaited and awaiter are both this origin, planted into
   the store, is the store the abstract callback returns. *)
LEMMA CallbackLift ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.awaited.origin = o,
           req.awaiter.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  LET c == HandlePromiseRegisterCallback(req, doc, t)
                a == P!HandlePromiseRegisterCallback(base, req, t)
            IN  IF a = {} THEN c.doc = doc
                ELSE a = {Plant(base, o, c.doc)}
PROOF
    <1> DEFINE c == HandlePromiseRegisterCallback(req, doc, t)
    <1> DEFINE a == P!HandlePromiseRegisterCallback(base, req, t)
    <1> DEFINE id == req.awaited
    <1> DEFINE who == req.awaiter
    <1>1. CASE id \notin DOMAIN doc \/ who \notin DOMAIN doc
        <2>1. id \notin DOMAIN base \/ who \notin DOMAIN base
            BY <1>1, Zenon DEF id, who
        <2>2. c = Skip(doc) /\ a = {}
            BY <1>1, <2>1 DEF c, a, id, who, HandlePromiseRegisterCallback,
                   P!HandlePromiseRegisterCallback
        <2>3. QED
            BY <2>2 DEF Skip
    <1>2. CASE id \in DOMAIN doc /\ who \in DOMAIN doc
        <2>1. id \in DOMAIN base /\ who \in DOMAIN base
              /\ base[id] = doc[id] /\ base[who] = doc[who]
              /\ id.origin = o
            BY <1>2, Zenon DEF id, who
        <2>2. Project(doc[id], t) = P!Project(base[id], t)
              /\ Project(doc[who], t) = P!Project(base[who], t)
            BY <2>1, Isa DEF Project, P!Project, NoTime, P!NoTime, NoTask, P!NoTask
        <2> DEFINE awaited == Project(doc[id], t)
        <2> DEFINE awaiter == Project(doc[who], t)
        <2>3. IsExternal(awaited.promise) <=> P!IsExternal(awaited.promise)
            BY DEF IsExternal, P!IsExternal, awaited
        <2>4. CASE ~awaiter.promise.tags.targeted
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2, <2>4 DEF c, a, awaited, awaiter, id, who,
                       HandlePromiseRegisterCallback, P!HandlePromiseRegisterCallback
            <3>2. QED
                BY <3>1 DEF Skip
        <2>5. CASE ~IsExternal(awaited.promise)
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2, <2>3, <2>5 DEF c, a, awaited, awaiter, id, who,
                       HandlePromiseRegisterCallback, P!HandlePromiseRegisterCallback
            <3>2. QED
                BY <3>1 DEF Skip
        <2>6. CASE awaited.promise.state /= "pending"
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2, <2>6 DEF c, a, awaited, awaiter, id, who,
                       HandlePromiseRegisterCallback, P!HandlePromiseRegisterCallback
            <3>2. QED
                BY <3>1 DEF Skip
        <2>7. CASE awaiter.promise.state /= "pending"
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2, <2>7 DEF c, a, awaited, awaiter, id, who,
                       HandlePromiseRegisterCallback, P!HandlePromiseRegisterCallback
            <3>2. QED
                BY <3>1 DEF Skip
        <2>8. CASE awaiter.promise.tags.targeted
                 /\ IsExternal(awaited.promise)
                 /\ awaited.promise.state = "pending"
                 /\ awaiter.promise.state = "pending"
            <3> DEFINE nw == [awaited EXCEPT !.promise.callbacks = @ \cup {who}]
            <3>1. c.doc = Write(doc, id, nw)
                BY <1>2, <2>8 DEF c, awaited, awaiter, nw, id, who,
                       HandlePromiseRegisterCallback
            <3>2. a = {P!Write(base, id, nw)}
                BY <2>1, <2>2, <2>3, <2>8, Isa DEF a, awaited, awaiter, nw, id, who,
                       P!HandlePromiseRegisterCallback, IsExternal, P!IsExternal
            <3>3. Plant(base, o, Write(doc, id, nw)) = Write(base, id, nw)
                <4>1. ASSUME NEW ii, NEW obj,
                             ii = id, obj = nw, ii.origin = o
                      PROVE  Plant(base, o, Write(doc, ii, obj)) = Write(base, ii, obj)
                    BY <4>1, PlantWrite
                <4>2. QED
                    BY <2>1, <4>1, Zenon DEF id
            <3>4. Write(base, id, nw) = P!Write(base, id, nw)
                <4>1. ASSUME NEW ii, NEW obj,
                             ii = id, obj = nw
                      PROVE  Write(base, ii, obj) = P!Write(base, ii, obj)
                    BY <4>1 DEF Write, P!Write
                <4>2. QED
                    BY <4>1, Zenon DEF id
            <3>5. a = {Plant(base, o, c.doc)}
                BY <3>1, <3>2, <3>3, <3>4
            <3>6. QED
                BY <3>5
        <2>9. QED
            BY <2>4, <2>5, <2>6, <2>7, <2>8
    <1>3. QED
        BY <1>1, <1>2 DEF c, a

(* An acquire of this origin's id, planted into the store, is the store the
   abstract acquire returns. *)
LEMMA AcquireLift ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  LET c == HandleTaskAcquire(req, doc, t)
                a == P!HandleTaskAcquire(base, req, t)
            IN  IF a = {} THEN c.doc = doc
                ELSE a = {Plant(base, o, c.doc)}
PROOF
    <1> DEFINE c == HandleTaskAcquire(req, doc, t)
    <1> DEFINE a == P!HandleTaskAcquire(base, req, t)
    <1> DEFINE id == req.id
    <1>1. CASE id \notin DOMAIN doc
        <2>1. id \notin DOMAIN base
            BY <1>1, Zenon DEF id
        <2>2. c = Skip(doc) /\ a = {}
            BY <1>1, <2>1 DEF c, a, id, HandleTaskAcquire, P!HandleTaskAcquire
        <2>3. QED
            BY <2>2 DEF Skip
    <1>2. CASE id \in DOMAIN doc
        <2>1. id \in DOMAIN base /\ base[id] = doc[id] /\ id.origin = o
            BY <1>2, Zenon DEF id
        <2>2. Project(doc[id], t) = P!Project(base[id], t)
            BY <2>1, Isa DEF Project, P!Project, NoTime, P!NoTime, NoTask, P!NoTask
        <2> DEFINE old == Project(doc[id], t)
        <2>3. CASE \/ old.task.state /= "pending"
                    \/ old.promise.state /= "pending"
                    \/ old.task.version /= req.version
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2, <2>3 DEF c, a, old, id,
                       HandleTaskAcquire, P!HandleTaskAcquire
            <3>2. QED
                BY <3>1 DEF Skip
        <2>4. CASE old.task.state = "pending"
                 /\ old.promise.state = "pending"
                 /\ old.task.version = req.version
            <3> DEFINE nw ==
                    [old EXCEPT !.task.state          = "acquired",
                                !.task.version        = @ + 1,
                                !.task.ttl            = req.ttl,
                                !.task.pid            = req.pid,
                                !.task.leaseTimeoutAt = t + req.ttl,
                                !.task.retryTimeoutAt = NoTime,
                                !.task.resumes        = {}]
            <3>1. NoTime = P!NoTime
                BY DEF NoTime, P!NoTime
            <3>2. nw = [old EXCEPT !.task.state          = "acquired",
                                   !.task.version        = @ + 1,
                                   !.task.ttl            = req.ttl,
                                   !.task.pid            = req.pid,
                                   !.task.leaseTimeoutAt = t + req.ttl,
                                   !.task.retryTimeoutAt = P!NoTime,
                                   !.task.resumes        = {}]
                BY <3>1 DEF nw
            <3>3. c.doc = Write(doc, id, nw)
                BY <1>2, <2>4 DEF c, old, nw, id, HandleTaskAcquire
            <3>4. a = {P!Write(base, id, nw)}
                BY <2>1, <2>2, <2>4, <3>2 DEF a, old, nw, id, P!HandleTaskAcquire
            <3>5. Plant(base, o, Write(doc, id, nw)) = Write(base, id, nw)
                <4>1. ASSUME NEW ii, NEW obj,
                             ii = id, obj = nw, ii.origin = o
                      PROVE  Plant(base, o, Write(doc, ii, obj)) = Write(base, ii, obj)
                    BY <4>1, PlantWrite
                <4>2. QED
                    BY <2>1, <4>1, Zenon DEF id
            <3>6. Write(base, id, nw) = P!Write(base, id, nw)
                <4>1. ASSUME NEW ii, NEW obj,
                             ii = id, obj = nw
                      PROVE  Write(base, ii, obj) = P!Write(base, ii, obj)
                    BY <4>1 DEF Write, P!Write
                <4>2. QED
                    BY <4>1, Zenon DEF id
            <3>7. a = {Plant(base, o, c.doc)}
                BY <3>3, <3>4, <3>5, <3>6
            <3>8. QED
                BY <3>7
        <2>5. QED
            BY <2>3, <2>4
    <1>3. QED
        BY <1>1, <1>2 DEF c, a

(* A release of this origin's id, planted into the store, is the store the
   abstract release returns. *)
LEMMA ReleaseLift ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  LET c == HandleTaskRelease(req, doc, t)
                a == P!HandleTaskRelease(base, req, t)
            IN  IF a = {} THEN c.doc = doc
                ELSE a = {Plant(base, o, c.doc)}
PROOF
    <1> DEFINE c == HandleTaskRelease(req, doc, t)
    <1> DEFINE a == P!HandleTaskRelease(base, req, t)
    <1> DEFINE id == req.id
    <1>1. CASE id \notin DOMAIN doc
        <2>1. id \notin DOMAIN base
            BY <1>1, Zenon DEF id
        <2>2. c = Skip(doc) /\ a = {}
            BY <1>1, <2>1 DEF c, a, id, HandleTaskRelease, P!HandleTaskRelease
        <2>3. QED
            BY <2>2 DEF Skip
    <1>2. CASE id \in DOMAIN doc
        <2>1. id \in DOMAIN base /\ base[id] = doc[id] /\ id.origin = o
            BY <1>2, Zenon DEF id
        <2>2. Project(doc[id], t) = P!Project(base[id], t)
            BY <2>1, Isa DEF Project, P!Project, NoTime, P!NoTime, NoTask, P!NoTask
        <2> DEFINE old == Project(doc[id], t)
        <2>3. CASE \/ old.task.state /= "acquired"
                    \/ old.promise.state /= "pending"
                    \/ old.task.version /= req.version
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2, <2>3 DEF c, a, old, id,
                       HandleTaskRelease, P!HandleTaskRelease
            <3>2. QED
                BY <3>1 DEF Skip
        <2>4. CASE old.task.state = "acquired"
                 /\ old.promise.state = "pending"
                 /\ old.task.version = req.version
            <3> DEFINE nw ==
                    [old EXCEPT !.task.state          = "pending",
                                !.task.pid            = NoPid,
                                !.task.ttl            = NoTime,
                                !.task.leaseTimeoutAt = NoTime,
                                !.task.retryTimeoutAt = t]
            <3> DEFINE oldA == P!Project(base[id], t)
            <3> DEFINE nwA ==
                    [oldA EXCEPT !.task.state          = "pending",
                                 !.task.pid            = NoPid,
                                 !.task.ttl            = P!NoTime,
                                 !.task.leaseTimeoutAt = P!NoTime,
                                 !.task.retryTimeoutAt = t]
            <3>1. NoTime = P!NoTime
                BY DEF NoTime, P!NoTime
            <3>2. oldA = old /\ nwA = nw
                BY <2>2, <3>1, Isa DEF old, oldA, nw, nwA, NoTime, P!NoTime
            <3>3. c.doc = Write(doc, id, nw)
                BY <1>2, <2>4, Isa DEF c, old, nw, id, HandleTaskRelease, Skip
            <3>4. a = {P!Write(base, id, nwA)}
                BY <2>1, <2>4, <3>2, Isa DEF a, old, oldA, nwA, id, P!HandleTaskRelease
            <3>5. Plant(base, o, Write(doc, id, nw)) = Write(base, id, nw)
                <4>1. ASSUME NEW ii, NEW obj,
                             ii = id, obj = nw, ii.origin = o
                      PROVE  Plant(base, o, Write(doc, ii, obj)) = Write(base, ii, obj)
                    BY <4>1, PlantWrite
                <4>2. QED
                    BY <2>1, <4>1, Zenon DEF id
            <3>6. Write(base, id, nw) = P!Write(base, id, nw)
                <4>1. ASSUME NEW ii, NEW obj,
                             ii = id, obj = nw
                      PROVE  Write(base, ii, obj) = P!Write(base, ii, obj)
                    BY <4>1 DEF Write, P!Write
                <4>2. QED
                    BY <4>1, Zenon DEF id
            <3>7. Write(base, id, nw) = P!Write(base, id, nwA)
                BY <3>2, <3>6, Zenon, Isa DEF P!Write
            <3>8. a = {Plant(base, o, c.doc)}
                BY <3>3, <3>4, <3>5, <3>7
            <3>9. QED
                BY <3>8
        <2>5. QED
            BY <2>3, <2>4
    <1>3. QED
        BY <1>1, <1>2 DEF c, a

(* A halt of this origin's id, planted into the store, is the store the
   abstract halt returns. *)
LEMMA HaltLift ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  LET c == HandleTaskHalt(req, doc, t)
                a == P!HandleTaskHalt(base, req, t)
            IN  IF a = {} THEN c.doc = doc
                ELSE a = {Plant(base, o, c.doc)}
PROOF
    <1> DEFINE c == HandleTaskHalt(req, doc, t)
    <1> DEFINE a == P!HandleTaskHalt(base, req, t)
    <1> DEFINE id == req.id
    <1>1. CASE id \notin DOMAIN doc
        <2>1. id \notin DOMAIN base
            BY <1>1, Zenon DEF id
        <2>2. c = Skip(doc) /\ a = {}
            BY <1>1, <2>1 DEF c, a, id, HandleTaskHalt, P!HandleTaskHalt
        <2>3. QED
            BY <2>2 DEF Skip
    <1>2. CASE id \in DOMAIN doc
        <2>1. id \in DOMAIN base /\ base[id] = doc[id] /\ id.origin = o
            BY <1>2, Zenon DEF id
        <2>2. Project(doc[id], t) = P!Project(base[id], t)
            BY <2>1, Isa DEF Project, P!Project, NoTime, P!NoTime, NoTask, P!NoTask
        <2> DEFINE old == Project(doc[id], t)
        <2>3. CASE old.task.state \in {"none", "fulfilled", "halted"}
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2, <2>3 DEF c, a, old, id,
                       HandleTaskHalt, P!HandleTaskHalt
            <3>2. QED
                BY <3>1 DEF Skip
        <2>4. CASE old.task.state \notin {"none", "fulfilled", "halted"}
            <3> DEFINE nw ==
                    [old EXCEPT !.task.state          = "halted",
                                !.task.pid            = NoPid,
                                !.task.ttl            = NoTime,
                                !.task.leaseTimeoutAt = NoTime,
                                !.task.retryTimeoutAt = NoTime]
            <3>1. NoTime = P!NoTime
                BY DEF NoTime, P!NoTime
            <3>2. nw = [old EXCEPT !.task.state          = "halted",
                                   !.task.pid            = NoPid,
                                   !.task.ttl            = P!NoTime,
                                   !.task.leaseTimeoutAt = P!NoTime,
                                   !.task.retryTimeoutAt = P!NoTime]
                BY <3>1 DEF nw
            <3>3. c.doc = Write(doc, id, nw)
                BY <1>2, <2>4 DEF c, old, nw, id, HandleTaskHalt
            <3>4. a = {P!Write(base, id, nw)}
                BY <2>1, <2>2, <2>4, <3>2 DEF a, old, nw, id, P!HandleTaskHalt
            <3>5. Plant(base, o, Write(doc, id, nw)) = Write(base, id, nw)
                <4>1. ASSUME NEW ii, NEW obj,
                             ii = id, obj = nw, ii.origin = o
                      PROVE  Plant(base, o, Write(doc, ii, obj)) = Write(base, ii, obj)
                    BY <4>1, PlantWrite
                <4>2. QED
                    BY <2>1, <4>1, Zenon DEF id
            <3>6. Write(base, id, nw) = P!Write(base, id, nw)
                <4>1. ASSUME NEW ii, NEW obj,
                             ii = id, obj = nw
                      PROVE  Write(base, ii, obj) = P!Write(base, ii, obj)
                    BY <4>1 DEF Write, P!Write
                <4>2. QED
                    BY <4>1, Zenon DEF id
            <3>7. a = {Plant(base, o, c.doc)}
                BY <3>3, <3>4, <3>5, <3>6
            <3>8. QED
                BY <3>7
        <2>5. QED
            BY <2>3, <2>4
    <1>3. QED
        BY <1>1, <1>2 DEF c, a

(* A continue of this origin's id, planted into the store, is the store the
   abstract continue returns. *)
LEMMA ContinueLift ==
    ASSUME NEW base, NEW o, NEW doc, NEW req, NEW t,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           req.id.origin = o,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  LET c == HandleTaskContinue(req, doc, t)
                a == P!HandleTaskContinue(base, req, t)
            IN  IF a = {} THEN c.doc = doc
                ELSE a = {Plant(base, o, c.doc)}
PROOF
    <1> DEFINE c == HandleTaskContinue(req, doc, t)
    <1> DEFINE a == P!HandleTaskContinue(base, req, t)
    <1> DEFINE id == req.id
    <1>1. CASE id \notin DOMAIN doc
        <2>1. id \notin DOMAIN base
            BY <1>1, Zenon DEF id
        <2>2. c = Skip(doc) /\ a = {}
            BY <1>1, <2>1 DEF c, a, id, HandleTaskContinue, P!HandleTaskContinue
        <2>3. QED
            BY <2>2 DEF Skip
    <1>2. CASE id \in DOMAIN doc
        <2>1. id \in DOMAIN base /\ base[id] = doc[id] /\ id.origin = o
            BY <1>2, Zenon DEF id
        <2>2. Project(doc[id], t) = P!Project(base[id], t)
            BY <2>1, Isa DEF Project, P!Project, NoTime, P!NoTime, NoTask, P!NoTask
        <2> DEFINE old == Project(doc[id], t)
        <2>3. CASE old.task.state /= "halted" \/ old.promise.state /= "pending"
            <3>1. c = Skip(doc) /\ a = {}
                BY <1>2, <2>1, <2>2, <2>3 DEF c, a, old, id,
                       HandleTaskContinue, P!HandleTaskContinue
            <3>2. QED
                BY <3>1 DEF Skip
        <2>4. CASE old.task.state = "halted" /\ old.promise.state = "pending"
            <3> DEFINE nw ==
                    [old EXCEPT !.task.state          = "pending",
                                !.task.pid            = NoPid,
                                !.task.ttl            = NoTime,
                                !.task.leaseTimeoutAt = NoTime,
                                !.task.retryTimeoutAt = t]
            <3>1. NoTime = P!NoTime
                BY DEF NoTime, P!NoTime
            <3>2. nw = [old EXCEPT !.task.state          = "pending",
                                   !.task.pid            = NoPid,
                                   !.task.ttl            = P!NoTime,
                                   !.task.leaseTimeoutAt = P!NoTime,
                                   !.task.retryTimeoutAt = t]
                BY <3>1 DEF nw
            <3>3. c.doc = Write(doc, id, nw)
                BY <1>2, <2>4 DEF c, old, nw, id, HandleTaskContinue
            <3>4. a = {P!Write(base, id, nw)}
                BY <2>1, <2>2, <2>4, <3>2 DEF a, old, nw, id, P!HandleTaskContinue
            <3>5. Plant(base, o, Write(doc, id, nw)) = Write(base, id, nw)
                <4>1. ASSUME NEW ii, NEW obj,
                             ii = id, obj = nw, ii.origin = o
                      PROVE  Plant(base, o, Write(doc, ii, obj)) = Write(base, ii, obj)
                    BY <4>1, PlantWrite
                <4>2. QED
                    BY <2>1, <4>1, Zenon DEF id
            <3>6. Write(base, id, nw) = P!Write(base, id, nw)
                <4>1. ASSUME NEW ii, NEW obj,
                             ii = id, obj = nw
                      PROVE  Write(base, ii, obj) = P!Write(base, ii, obj)
                    BY <4>1 DEF Write, P!Write
                <4>2. QED
                    BY <4>1, Zenon DEF id
            <3>7. a = {Plant(base, o, c.doc)}
                BY <3>3, <3>4, <3>5, <3>6
            <3>8. QED
                BY <3>7
        <2>5. QED
            BY <2>3, <2>4
    <1>3. QED
        BY <1>1, <1>2 DEF c, a

=============================================================================
