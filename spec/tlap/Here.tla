------------------------------ MODULE Here --------------------------------
(* The timeout pass of one document is the image of that document's due
   promises. The chain for any finite subset of those promises is already
   TimeoutSub. *)
EXTENDS CallOn

LEMMA TimeoutDoc ==
    ASSUME NEW doc, NEW t, NEW S,
           S = { i \in DOMAIN doc :
                   /\ doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t }
    PROVE  SweepTimeoutAt(doc, t).doc = Image(doc, S, t)
PROOF
    <1>1. CASE S = {}
        <2>1. SweepTimeoutAt(doc, t).doc = doc
            BY <1>1 DEF SweepTimeoutAt
        <2>2. Image(doc, S, t) = doc
            BY <1>1 DEF Image
        <2>3. QED
            BY <2>1, <2>2
    <1>2. CASE S # {}
        <2> DEFINE sw == SweepTimeoutAt(doc, t).doc
        <2> DEFINE im ==
                [ i \in DOMAIN doc |->
                    IF i \in S THEN P!Project(doc[i], t) ELSE doc[i] ]
        <2>1. Image(doc, S, t) = im
            BY <1>2 DEF Image, BulkP, im
        <2>2. sw = [ i \in DOMAIN doc |->
                       IF i \in S THEN Project(doc[i], t) ELSE doc[i] ]
            BY <1>2 DEF sw, SweepTimeoutAt
        <2>3. \A i \in DOMAIN doc : Project(doc[i], t) = P!Project(doc[i], t)
            <3> SUFFICES ASSUME NEW i \in DOMAIN doc
                         PROVE  Project(doc[i], t) = P!Project(doc[i], t)
                OBVIOUS
            <3>1. QED
                BY SameProject
        <2>4. \A i \in DOMAIN doc :
                (IF i \in S THEN Project(doc[i], t) ELSE doc[i])
                  = (IF i \in S THEN P!Project(doc[i], t) ELSE doc[i])
            BY <2>3
        <2>5. sw = im
            BY <2>2, <2>4, ExtCtor DEF im
        <2>6. QED
            BY <2>1, <2>5 DEF sw
    <1>3. QED
        BY <1>1, <1>2

LEMMA LeaseDoc ==
    ASSUME NEW doc, NEW t, NEW S,
           S = { i \in DOMAIN doc :
                   doc[i].task.state = "acquired"
                   /\ doc[i].task.leaseTimeoutAt <= t }
    PROVE  SweepExpiresAt(doc, t).doc = ImgL(doc, S, t)
PROOF
    <1>1. CASE S = {}
        <2>1. SweepExpiresAt(doc, t).doc = doc
            BY <1>1 DEF SweepExpiresAt
        <2>2. ImgL(doc, S, t) = doc
            BY <1>1 DEF ImgL
        <2>3. QED
            BY <2>1, <2>2
    <1>2. CASE S # {}
        <2> DEFINE sw == SweepExpiresAt(doc, t).doc
        <2> DEFINE im ==
                [ i \in DOMAIN doc |->
                    IF i \in S THEN LeaseBody(doc[i], t) ELSE doc[i] ]
        <2>1. ImgL(doc, S, t) = im
            BY <1>2 DEF ImgL, im
        <2>2. sw = im
            BY <1>2 DEF sw, SweepExpiresAt, LeaseBody, im
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2

LEMMA RetryDoc ==
    ASSUME NEW doc, NEW t, NEW S,
           S = { i \in DOMAIN doc :
                   doc[i].task.state = "pending"
                   /\ doc[i].task.retryTimeoutAt <= t }
    PROVE  SweepRetryAt(doc, t).doc = ImgR(doc, S, t)
PROOF
    <1>1. CASE S = {}
        <2>1. SweepRetryAt(doc, t).doc = doc
            BY <1>1 DEF SweepRetryAt
        <2>2. ImgR(doc, S, t) = doc
            BY <1>1 DEF ImgR
        <2>3. QED
            BY <2>1, <2>2
    <1>2. CASE S # {}
        <2> DEFINE sw == SweepRetryAt(doc, t).doc
        <2> DEFINE im ==
                [ i \in DOMAIN doc |->
                    IF i \in S THEN RetryBody(doc[i], t) ELSE doc[i] ]
        <2>1. ImgR(doc, S, t) = im
            BY <1>2 DEF ImgR, im
        <2>2. sw = im
            BY <1>2 DEF sw, SweepRetryAt, RetryBody, im
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2

(* A listener pass on one document drops every address of a settled
   promise. That is the image of the due pairs, once projection is already
   the identity and every listener address is an address. *)

LEMMA DropIsStruck ==
    ASSUME NEW obj
    PROVE  DropListeners(obj) = Struck(obj, obj.promise.listeners)
PROOF
    <1>1. obj.promise.listeners \ obj.promise.listeners = {}
        BY Z3
    <1>2. DropListeners(obj) = P!WithoutListeners(obj, obj.promise.listeners)
        BY <1>1, Zenon DEF DropListeners, P!WithoutListeners
    <1>3. QED
        BY <1>2, SameStruck

LEMMA SamePairs ==
    ASSUME NEW doc, NEW t,
           \A i \in DOMAIN doc : P!Project(doc[i], t) = doc[i]
    PROVE  DueN(doc, t)
              = { x \in [id : { i \in DOMAIN doc :
                                  doc[i].promise.state /= "pending" },
                         address : Address] :
                    x.address \in doc[x.id].promise.listeners }
PROOF
    <1> DEFINE non == { i \in DOMAIN doc : doc[i].promise.state /= "pending" }
    <1> DEFINE got ==
            { x \in [id : non, address : Address] :
                x.address \in doc[x.id].promise.listeners }
    <1>1. \A j \in DOMAIN doc :
            P!Project(doc[j], t).promise.state = doc[j].promise.state
        <2> SUFFICES ASSUME NEW j \in DOMAIN doc
                     PROVE  P!Project(doc[j], t).promise.state = doc[j].promise.state
            OBVIOUS
        <2>1. P!Project(doc[j], t) = doc[j]
            OBVIOUS
        <2>2. QED
            BY <2>1
    <1>2. Ids(doc, t) = non
        BY <1>1, Z3 DEF Ids, non
    <1>3. QED
        BY <1>2 DEF DueN, got

LEMMA LisPairs ==
    ASSUME NEW non, NEW doc, NEW S,
           S = { x \in [id : non, address : Address] :
                   x.address \in doc[x.id].promise.listeners }
    PROVE  S \subseteq [id : non, address : Address]
PROOF
    BY Z3

LEMMA GoneMem ==
    ASSUME NEW i, NEW S, NEW ad
    PROVE  ad \in Gone(i, S) <=> ad \in Address /\ [id |-> i, address |-> ad] \in S
PROOF
    BY DEF Gone

LEMMA GoneOut ==
    ASSUME NEW j, NEW non, NEW S,
           j \notin non,
           S \subseteq [id : non, address : Address]
    PROVE  Gone(j, S) = {}
PROOF
    <1>1. \A ad : ad \notin Gone(j, S)
        <2> SUFFICES ASSUME NEW ad
                     PROVE  ad \notin Gone(j, S)
            OBVIOUS
        <2>1. CASE ad \notin Address
            BY <2>1, GoneMem
        <2>2. CASE ad \in Address
            <3> DEFINE rec == [id |-> j, address |-> ad]
            <3>1. rec.id = j
                BY DEF rec
            <3>2. rec \notin [id : non, address : Address]
                BY <3>1, Z3
            <3>3. rec \notin S
                BY <3>2
            <3>4. rec = [id |-> j, address |-> ad]
                BY DEF rec
            <3>5. QED
                BY <2>2, <3>3, <3>4, GoneMem
        <2>3. QED
            BY <2>1, <2>2
    <1>2. QED
        BY <1>1, Z3

LEMMA InComp ==
    ASSUME NEW non, NEW doc, NEW S, NEW x,
           S = { y \in [id : non, address : Address] :
                   y.address \in doc[y.id].promise.listeners }
    PROVE  x \in S <=> x \in [id : non, address : Address]
                      /\ x.address \in doc[x.id].promise.listeners
PROOF
    BY Z3

LEMMA GoneAll ==
    ASSUME NEW doc, NEW i, NEW non, NEW S,
           i \in non,
           non \subseteq DOMAIN doc,
           doc[i].promise.listeners \subseteq Address,
           S = { x \in [id : non, address : Address] :
                   x.address \in doc[x.id].promise.listeners }
    PROVE  Gone(i, S) = doc[i].promise.listeners
PROOF
    <1> DEFINE lis == doc[i].promise.listeners
    <1>1. \A ad : ad \in Gone(i, S) <=> ad \in lis
        <2> SUFFICES ASSUME NEW ad
                     PROVE  ad \in Gone(i, S) <=> ad \in lis
            OBVIOUS
        <2> DEFINE rec == [id |-> i, address |-> ad]
        <2>1. ad \in Gone(i, S) <=> ad \in Address /\ rec \in S
            BY GoneMem DEF rec
        <2>2. rec.id = i /\ rec.address = ad
            BY DEF rec
        <2>3. ASSUME ad \in lis
              PROVE  ad \in Gone(i, S)
            <3>1. ad \in Address
                BY <2>3 DEF lis
            <3>2. rec \in [id : non, address : Address]
                BY <3>1, Z3 DEF rec
            <3>3. rec.address \in doc[rec.id].promise.listeners
                BY <2>2, <2>3 DEF lis
            <3>4. rec \in S
                BY <3>2, <3>3, InComp
            <3>5. QED
                BY <2>1, <3>1, <3>4
        <2>4. ASSUME ad \in Gone(i, S)
              PROVE  ad \in lis
            <3>1. ad \in Address /\ rec \in S
                BY <2>1, <2>4
            <3>2. rec.address \in doc[rec.id].promise.listeners
                BY <3>1, InComp
            <3>3. QED
                BY <2>2, <3>2 DEF lis
        <2>5. QED
            BY <2>3, <2>4
    <1>2. QED
        BY <1>1, SetExtensionality DEF lis

LEMMA BodyWhen ==
    ASSUME NEW o, NEW Q, NEW j
    PROVE  BodyN(o, Q, j)
              = (LET g == Gone(j, Q)
                 IN  IF g = {} THEN o[j] ELSE Struck(o[j], g))
PROOF
    BY ONLY Isa DEF BodyN

LEMMA ListenAtDoc ==
    ASSUME NEW doc, NEW j, NEW non, NEW due,
           j \in DOMAIN doc,
           non = { i \in DOMAIN doc : doc[i].promise.state /= "pending" },
           due = { x \in [id : non, address : Address] :
                     x.address \in doc[x.id].promise.listeners },
           doc[j].promise.listeners \subseteq Address
    PROVE  BodyN(doc, due, j)
              = IF doc[j].promise.state /= "pending"
                   /\ doc[j].promise.listeners /= {}
                THEN DropListeners(doc[j])
                ELSE doc[j]
PROOF
    <1>1. due \subseteq [id : non, address : Address]
        BY LisPairs
    <1>2. non \subseteq DOMAIN doc
        BY Z3
    <1>3. CASE doc[j].promise.state = "pending"
        <2>1. j \notin non
            BY <1>3, Z3
        <2>2. Gone(j, due) = {}
            BY <1>1, <2>1, GoneOut
        <2>3. BodyN(doc, due, j) = doc[j]
            BY <2>2, BodyWhen
        <2>4. QED
            BY <1>3, <2>3
    <1>4. CASE doc[j].promise.state /= "pending" /\ doc[j].promise.listeners = {}
        <2>1. j \in non
            BY <1>4, Z3
        <2>2. Gone(j, due) = doc[j].promise.listeners
            BY <1>2, <2>1, GoneAll
        <2>3. Gone(j, due) = {}
            BY <1>4, <2>2
        <2>4. BodyN(doc, due, j) = doc[j]
            BY <2>3, BodyWhen
        <2>5. QED
            BY <1>4, <2>4
    <1>5. CASE doc[j].promise.state /= "pending" /\ doc[j].promise.listeners /= {}
        <2>1. j \in non
            BY <1>5, Z3
        <2>2. Gone(j, due) = doc[j].promise.listeners
            BY <1>2, <2>1, GoneAll
        <2>3. Gone(j, due) /= {}
            BY <1>5, <2>2
        <2>4. BodyN(doc, due, j) = Struck(doc[j], Gone(j, due))
            BY <2>3, BodyWhen
        <2>5. Struck(doc[j], Gone(j, due)) = DropListeners(doc[j])
            BY <2>2, DropIsStruck
        <2>6. QED
            BY <1>5, <2>4, <2>5
    <1>6. QED
        BY <1>3, <1>4, <1>5

LEMMA SweepLisEq ==
    ASSUME NEW doc, NEW t
    PROVE  LET pairs ==
                { x \in [id : { i \in DOMAIN doc :
                                  doc[i].promise.state /= "pending" },
                         address : Address] :
                    x.address \in doc[x.id].promise.listeners }
           IN  SweepListeners(doc, t).doc
                 = IF pairs = {} THEN doc
                   ELSE [ i \in DOMAIN doc |->
                            IF doc[i].promise.state /= "pending"
                               /\ doc[i].promise.listeners /= {}
                            THEN DropListeners(doc[i])
                            ELSE doc[i] ]
PROOF
    BY ONLY DEF SweepListeners

LEMMA ListenDoc ==
    ASSUME NEW doc, NEW t,
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address,
           \A k \in DOMAIN doc : P!Project(doc[k], t) = doc[k]
    PROVE  SweepListeners(doc, t).doc = ImgN(doc, DueN(doc, t))
PROOF
    <1> DEFINE non == { i \in DOMAIN doc : doc[i].promise.state /= "pending" }
    <1> DEFINE due ==
            { x \in [id : non, address : Address] :
                x.address \in doc[x.id].promise.listeners }
    <1>1. DueN(doc, t) = due
        BY SamePairs DEF non, due
    <1>2. SweepListeners(doc, t).doc
            = IF due = {} THEN doc
              ELSE [ i \in DOMAIN doc |->
                       IF doc[i].promise.state /= "pending"
                          /\ doc[i].promise.listeners /= {}
                       THEN DropListeners(doc[i])
                       ELSE doc[i] ]
        BY SweepLisEq DEF non, due
    <1>3. CASE due = {}
        <2>1. ImgN(doc, DueN(doc, t)) = doc
            BY <1>1, <1>3 DEF ImgN
        <2>2. QED
            BY <1>2, <1>3, <2>1
    <1>4. CASE due # {}
        <2> DEFINE im == [ i \in DOMAIN doc |-> BodyN(doc, due, i) ]
        <2>1. ImgN(doc, DueN(doc, t)) = im
            BY <1>1, <1>4 DEF ImgN, im
        <2>2. \A j \in DOMAIN doc :
                (IF doc[j].promise.state /= "pending"
                    /\ doc[j].promise.listeners /= {}
                 THEN DropListeners(doc[j])
                 ELSE doc[j])
                  = BodyN(doc, due, j)
            <3> SUFFICES ASSUME NEW j \in DOMAIN doc
                         PROVE  (IF doc[j].promise.state /= "pending"
                                    /\ doc[j].promise.listeners /= {}
                                 THEN DropListeners(doc[j])
                                 ELSE doc[j])
                                  = BodyN(doc, due, j)
                OBVIOUS
            <3>1. doc[j].promise.listeners \subseteq Address
                OBVIOUS
            <3>2. QED
                BY <3>1, ListenAtDoc DEF non, due
        <2>3. [ i \in DOMAIN doc |->
                  IF doc[i].promise.state /= "pending"
                     /\ doc[i].promise.listeners /= {}
                  THEN DropListeners(doc[i])
                  ELSE doc[i] ]
                = im
            BY <2>2, ExtCtor DEF im
        <2>4. QED
            BY <1>2, <1>4, <2>1, <2>3
    <1>5. QED
        BY <1>3, <1>4

=============================================================================== 
