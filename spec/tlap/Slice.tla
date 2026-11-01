------------------------------- MODULE Slice -------------------------------
(* One origin's timeout pass, planted into the whole store, is the timeout
   chain of that origin's due promises. The other origins stay. *)
EXTENDS Plant

LEMMA PlantId ==
    ASSUME NEW base, NEW o, NEW doc,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  Plant(base, o, doc) = base
PROOF
    <1> DEFINE kept == { j \in DOMAIN base : j.origin /= o }
    <1> DEFINE dom == kept \cup DOMAIN doc
    <1>1. \A i : i \in dom <=> i \in DOMAIN base
        BY DEF kept, dom
    <1>2. dom = DOMAIN base
        BY <1>1, SetExtensionality DEF dom
    <1>3. \A i \in DOMAIN base :
            (IF i \in DOMAIN doc THEN doc[i] ELSE base[i]) = base[i]
        BY Z3
    <1>4. Plant(base, o, doc)
            = [ i \in dom |-> IF i \in DOMAIN doc THEN doc[i] ELSE base[i] ]
        BY DEF Plant, kept, dom
    <1>5. [ i \in dom |-> IF i \in DOMAIN doc THEN doc[i] ELSE base[i] ]
            = [ i \in DOMAIN base |-> base[i] ]
        BY <1>2, <1>3, ExtCtor
    <1>6. QED
        BY <1>4, <1>5

LEMMA PlantImage ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW S,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           S \subseteq DOMAIN doc,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  Plant(base, o, Image(doc, S, t)) = Image(base, S, t)
PROOF
    <1>1. CASE S = {}
        <2>1. Image(doc, S, t) = doc /\ Image(base, S, t) = base
            BY <1>1 DEF Image
        <2>2. Plant(base, o, doc) = base
            BY PlantId
        <2>3. QED
            BY <2>1, <2>2
    <1>2. CASE S # {}
        <2> DEFINE body ==
                [ i \in DOMAIN doc |->
                    IF i \in S THEN P!Project(doc[i], t) ELSE doc[i] ]
        <2> DEFINE full ==
                [ i \in DOMAIN base |->
                    IF i \in S THEN P!Project(base[i], t) ELSE base[i] ]
        <2>1. Image(doc, S, t) = body
            BY <1>2 DEF Image, BulkP, body
        <2>2. Image(base, S, t) = full
            BY <1>2 DEF Image, BulkP, full
        <2>3. DOMAIN body = DOMAIN doc
            BY DomCtor DEF body
        <2> DEFINE kept == { j \in DOMAIN base : j.origin /= o }
        <2> DEFINE dom == kept \cup DOMAIN body
        <2>4. \A i : i \in dom <=> i \in DOMAIN base
            BY <2>3 DEF kept, dom
        <2>5. dom = DOMAIN base
            BY <2>4, SetExtensionality DEF dom
        <2>6. \A i \in DOMAIN base :
                (IF i \in DOMAIN body THEN body[i] ELSE base[i]) = full[i]
            <3> SUFFICES ASSUME NEW k \in DOMAIN base
                         PROVE  (IF k \in DOMAIN body THEN body[k] ELSE base[k])
                                  = full[k]
                OBVIOUS
            <3>1. k \in DOMAIN doc => base[k] = doc[k]
                BY <2>3
            <3>2. QED
                BY <2>3, <3>1, Zenon DEF body, full
        <2>7. Plant(base, o, body)
                = [ i \in dom |-> IF i \in DOMAIN body THEN body[i] ELSE base[i] ]
            BY DEF Plant, kept, dom
        <2>8. [ i \in dom |-> IF i \in DOMAIN body THEN body[i] ELSE base[i] ]
                = full
            BY <2>5, <2>6, ExtCtor DEF full
        <2>9. QED
            BY <2>1, <2>2, <2>7, <2>8
    <1>3. QED
        BY <1>1, <1>2

LEMMA DueSlice ==
    ASSUME NEW base, NEW doc, NEW o, NEW t, NEW S,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t }
    PROVE  S \subseteq DueP(base, t)
PROOF
    <1>1. ASSUME NEW k \in S
          PROVE  k \in DueP(base, t)
        <2>1. k \in DOMAIN doc
              /\ doc[k].promise.state = "pending"
              /\ doc[k].promise.timeoutAt <= t
            BY <1>1
        <2>2. k \in DOMAIN base /\ base[k] = doc[k]
            BY <2>1
        <2>3. base[k].promise.state = "pending"
              /\ base[k].promise.timeoutAt <= t
            BY <2>1, <2>2
        <2>4. QED
            BY <2>2, <2>3 DEF DueP
    <1>2. QED
        BY <1>1

LEMMA SubCap ==
    ASSUME NEW S, S \subseteq Id
    PROVE  /\ IsFiniteSet(S)
           /\ Cardinality(S) \in 0 .. P!MaxSweep
PROOF
    <1>1. IsFiniteSet(Id) /\ Cardinality(Id) <= P!MaxSweep /\ P!MaxSweep \in Nat
        BY FiniteOrigin, FiniteRest, IdFinite, SweepCap
    <1>2. IsFiniteSet(S) /\ Cardinality(S) <= Cardinality(Id)
        BY <1>1, FS_Subset
    <1>3. Cardinality(S) \in Nat /\ Cardinality(Id) \in Nat
        BY <1>1, <1>2, FS_CardinalityType
    <1>4. QED
        BY <1>1, <1>2, <1>3, Z3

LEMMA TimeoutPlant ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW S,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t },
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  Plant(base, o, SweepTimeoutAt(doc, t).doc) = Image(base, S, t)
PROOF
    <1>1. S \subseteq DOMAIN doc
        BY Zenon
    <1>2. SweepTimeoutAt(doc, t).doc = Image(doc, S, t)
        BY TimeoutDoc
    <1>3. QED
        BY <1>1, <1>2, PlantImage

LEMMA TimeoutChain ==
    ASSUME NEW base, NEW box, NEW o, NEW doc, NEW t, NEW S,
           DOMAIN base \subseteq Id,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t },
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  /\ ReachN(base, box, t,
                     Plant(base, o, SweepTimeoutAt(doc, t).doc),
                     box, Cardinality(S))
           /\ Cardinality(S) \in 0 .. P!MaxSweep
PROOF
    <1>1. S \subseteq DueP(base, t)
        BY DueSlice
    <1>2. S \subseteq Id
        BY <1>1, DueSubset, Z3
    <1>3. IsFiniteSet(S) /\ Cardinality(S) \in 0 .. P!MaxSweep
        BY <1>2, SubCap
    <1>4. Plant(base, o, SweepTimeoutAt(doc, t).doc) = Image(base, S, t)
        BY TimeoutPlant
    <1>5. ReachN(base, box, t, Image(base, S, t), box, Cardinality(S))
        BY <1>1, <1>3, TimeoutSub
    <1>6. QED
        BY <1>3, <1>4, <1>5

(* After the origin's own timeout image, every id of that document is
   already projected. Listener and callback passes ask for exactly that. *)
LEMMA SliceFixed ==
    ASSUME NEW doc, NEW t, NEW S,
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t }
    PROVE  \A k \in DOMAIN doc :
              P!Project(Image(doc, S, t)[k], t) = Image(doc, S, t)[k]
PROOF
    <1>1. S \subseteq DOMAIN doc
        BY Zenon
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  P!Project(Image(doc, S, t)[k], t) = Image(doc, S, t)[k]
        <2>1. /\ k \in DOMAIN Image(doc, S, t)
              /\ Image(doc, S, t)[k]
                   = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
            BY <1>1, <1>2, ImageVal
        <2>2. CASE k \in S
            <3>1. Image(doc, S, t)[k] = P!Project(doc[k], t)
                BY <2>1, <2>2
            <3>2. QED
                BY <3>1, ProjectTwice
        <2>3. CASE k \notin S
            <3>1. Image(doc, S, t)[k] = doc[k]
                BY <2>1, <2>3
            <3>2. \/ doc[k].promise.state /= "pending"
                  \/ ~(doc[k].promise.timeoutAt <= t)
                BY <1>2, <2>3, Zenon
            <3>3. P!Project(doc[k], t) = doc[k]
                BY <3>2, ProjectId
            <3>4. QED
                BY <3>1, <3>3
        <2>4. QED
            BY <2>2, <2>3
    <1>3. QED
        BY <1>2

LEMMA ListenersKept ==
    ASSUME NEW obj, NEW t
    PROVE  P!Project(obj, t).promise.listeners = obj.promise.listeners
PROOF
    <1>1. CASE obj.promise.state = "pending" /\ obj.promise.timeoutAt <= t
        <2> DEFINE p == P!Project(obj, t)
        <2> DEFINE st == IF obj.promise.tags.timer THEN "resolved"
                         ELSE "rejectedTimedout"
        <2> DEFINE p1 == [obj.promise EXCEPT !.state = st]
        <2> DEFINE p2 == [p1 EXCEPT !.value = NoValue]
        <2> DEFINE p3 == [p2 EXCEPT !.settledAt = obj.promise.timeoutAt]
        <2>1. p1.listeners = obj.promise.listeners
            BY ONLY Z3 DEF p1
        <2>2. p2.listeners = p1.listeners /\ p3.listeners = p2.listeners
            BY ONLY Z3 DEF p2, p3
        <2>3. p.promise = p3
            BY ONLY <1>1, Zenon DEF p, st, p1, p2, p3, P!Project
        <2>4. QED
            BY <2>1, <2>2, <2>3
    <1>2. CASE obj.promise.state /= "pending" \/ ~(obj.promise.timeoutAt <= t)
        BY <1>2, ProjectId
    <1>3. QED
        BY <1>1, <1>2

LEMMA ImageDom ==
    ASSUME NEW doc, NEW t, NEW S, S \subseteq DOMAIN doc
    PROVE  DOMAIN Image(doc, S, t) = DOMAIN doc
PROOF
    <1>1. CASE S = {}
        BY <1>1 DEF Image
    <1>2. CASE S # {}
        <2>1. Image(doc, S, t) = BulkP(doc, S, t)
            BY <1>2 DEF Image
        <2>2. DOMAIN BulkP(doc, S, t) = DOMAIN doc
            BY DomCtor DEF BulkP
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2

LEMMA ListenersOn ==
    ASSUME NEW doc, NEW t, NEW S,
           S \subseteq DOMAIN doc,
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address
    PROVE  \A k \in DOMAIN Image(doc, S, t) :
              Image(doc, S, t)[k].promise.listeners \subseteq Address
PROOF
    <1>1. DOMAIN Image(doc, S, t) = DOMAIN doc
        BY ImageDom
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  Image(doc, S, t)[k].promise.listeners \subseteq Address
        <2>1. /\ k \in DOMAIN Image(doc, S, t)
              /\ Image(doc, S, t)[k]
                   = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
            BY <1>2, ImageVal
        <2>2. CASE k \in S
            <3>1. Image(doc, S, t)[k].promise.listeners
                    = doc[k].promise.listeners
                BY <2>1, <2>2, ListenersKept
            <3>2. QED
                BY <1>2, <2>2, <3>1
        <2>3. CASE k \notin S
            BY <1>2, <2>1, <2>3
        <2>4. QED
            BY <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2

LEMMA ListenAfter ==
    ASSUME NEW doc, NEW t, NEW S,
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t },
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address
    PROVE  SweepListeners(Image(doc, S, t), t).doc
              = ImgN(Image(doc, S, t), DueN(Image(doc, S, t), t))
PROOF
    <1> DEFINE im == Image(doc, S, t)
    <1>1. S \subseteq DOMAIN doc
        BY Zenon
    <1>2. DOMAIN im = DOMAIN doc
        BY <1>1, ImageDom DEF im
    <1>3. \A k \in DOMAIN im : P!Project(im[k], t) = im[k]
        BY <1>2, SliceFixed DEF im
    <1>4. \A k \in DOMAIN im : im[k].promise.listeners \subseteq Address
        BY <1>1, ListenersOn DEF im
    <1>5. QED
        BY <1>3, <1>4, ListenDoc DEF im

LEMMA SameStruck ==
    ASSUME NEW a, NEW b, NEW G, a = b
    PROVE  Struck(a, G) = Struck(b, G)
PROOF
    BY ONLY Zenon DEF Struck

LEMMA SameBody ==
    ASSUME NEW a, NEW b, NEW Q, NEW j, a[j] = b[j]
    PROVE  BodyN(a, Q, j) = BodyN(b, Q, j)
PROOF
    <1>1. CASE Gone(j, Q) = {}
        <2>1. BodyN(a, Q, j)
                = (LET g == Gone(j, Q)
                   IN  IF g = {} THEN a[j] ELSE Struck(a[j], g))
            BY BodyWhen
        <2>2. BodyN(a, Q, j) = a[j]
            BY ONLY <1>1, <2>1, Zenon
        <2>3. BodyN(b, Q, j)
                = (LET g == Gone(j, Q)
                   IN  IF g = {} THEN b[j] ELSE Struck(b[j], g))
            BY BodyWhen
        <2>4. BodyN(b, Q, j) = b[j]
            BY ONLY <1>1, <2>3, Zenon
        <2>5. QED
            BY <2>2, <2>4
    <1>2. CASE Gone(j, Q) # {}
        <2>1. BodyN(a, Q, j)
                = (LET g == Gone(j, Q)
                   IN  IF g = {} THEN a[j] ELSE Struck(a[j], g))
            BY BodyWhen
        <2>2. BodyN(a, Q, j) = Struck(a[j], Gone(j, Q))
            BY ONLY <1>2, <2>1, Zenon
        <2>3. BodyN(b, Q, j)
                = (LET g == Gone(j, Q)
                   IN  IF g = {} THEN b[j] ELSE Struck(b[j], g))
            BY BodyWhen
        <2>4. BodyN(b, Q, j) = Struck(b[j], Gone(j, Q))
            BY ONLY <1>2, <2>3, Zenon
        <2>5. Struck(a[j], Gone(j, Q)) = Struck(b[j], Gone(j, Q))
            BY SameStruck
        <2>6. QED
            BY <2>2, <2>4, <2>5
    <1>3. QED
        BY <1>1, <1>2

LEMMA IdleBody ==
    ASSUME NEW store, NEW j, NEW non, NEW P,
           j \notin non,
           P \subseteq [id : non, address : Address]
    PROVE  BodyN(store, P, j) = store[j]
PROOF
    <1>1. Gone(j, P) = {}
        BY GoneOut
    <1>2. BodyN(store, P, j)
            = (LET g == Gone(j, P)
               IN  IF g = {} THEN store[j] ELSE Struck(store[j], g))
        BY BodyWhen
    <1>3. QED
        BY ONLY <1>1, <1>2, Zenon

(* A listener image of one document, planted, is the listener image of the
   whole store on those same pairs. Pairs outside the document are absent. *)
LEMMA PlantN ==
    ASSUME NEW base, NEW o, NEW doc, NEW P,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           base = [ i \in DOMAIN base |-> base[i] ],
           P \subseteq [id : DOMAIN doc, address : Address]
    PROVE  Plant(base, o, ImgN(doc, P)) = ImgN(base, P)
PROOF
    <1>1. CASE P = {}
        <2>1. ImgN(doc, P) = doc /\ ImgN(base, P) = base
            BY <1>1 DEF ImgN
        <2>2. Plant(base, o, doc) = base
            BY PlantId
        <2>3. QED
            BY <2>1, <2>2
    <1>2. CASE P # {}
        <2> DEFINE body == [ j \in DOMAIN doc |-> BodyN(doc, P, j) ]
        <2> DEFINE full == [ j \in DOMAIN base |-> BodyN(base, P, j) ]
        <2>1. ImgN(doc, P) = body
            BY <1>2 DEF ImgN, body
        <2>2. ImgN(base, P) = full
            BY <1>2 DEF ImgN, full
        <2>3. DOMAIN body = DOMAIN doc
            BY DomCtor DEF body
        <2> DEFINE kept == { q \in DOMAIN base : q.origin /= o }
        <2> DEFINE dom == kept \cup DOMAIN body
        <2>4. \A n : n \in dom <=> n \in DOMAIN base
            BY <2>3 DEF kept, dom
        <2>5. dom = DOMAIN base
            BY <2>4, SetExtensionality DEF dom
        <2>6. \A n \in DOMAIN base :
                (IF n \in DOMAIN body THEN body[n] ELSE base[n]) = full[n]
            <3> SUFFICES ASSUME NEW k \in DOMAIN base
                         PROVE  (IF k \in DOMAIN body THEN body[k] ELSE base[k])
                                  = full[k]
                OBVIOUS
            <3>1. full[k] = BodyN(base, P, k)
                BY Zenon DEF full
            <3>2. CASE k \in DOMAIN doc
                <4>1. k \in DOMAIN body /\ body[k] = BodyN(doc, P, k)
                    BY <2>3, <3>2, Zenon DEF body
                <4>2. base[k] = doc[k]
                    BY <3>2, Zenon
                <4>3. BodyN(base, P, k) = BodyN(doc, P, k)
                    BY <4>2, SameBody
                <4>4. QED
                    BY <3>1, <4>1, <4>3
            <3>3. CASE k \notin DOMAIN doc
                <4>1. k \notin DOMAIN body
                    BY <2>3, <3>3
                <4>2. BodyN(base, P, k) = base[k]
                    BY <3>3, IdleBody
                <4>3. QED
                    BY <3>1, <4>1, <4>2
            <3>4. QED
                BY <3>2, <3>3
        <2>7. Plant(base, o, body)
                = [ n \in dom |-> IF n \in DOMAIN body THEN body[n] ELSE base[n] ]
            BY DEF Plant, kept, dom
        <2>8. [ n \in dom |-> IF n \in DOMAIN body THEN body[n] ELSE base[n] ]
                = full
            BY <2>5, <2>6, ExtCtor DEF full
        <2>9. QED
            BY <2>1, <2>2, <2>7, <2>8
    <1>3. QED
        BY <1>1, <1>2

LEMMA EtaImage ==
    ASSUME NEW base, NEW t, NEW S,
           S \subseteq DOMAIN base,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  Image(base, S, t)
              = [ i \in DOMAIN Image(base, S, t) |-> Image(base, S, t)[i] ]
PROOF
    <1>1. CASE S = {}
        <2>1. Image(base, S, t) = base
            BY <1>1 DEF Image
        <2>2. DOMAIN Image(base, S, t) = DOMAIN base
            BY ImageDom
        <2>3. QED
            BY <2>1, <2>2, Zenon
    <1>2. CASE S # {}
        <2> DEFINE f ==
                [ i \in DOMAIN base |->
                    IF i \in S THEN P!Project(base[i], t) ELSE base[i] ]
        <2>1. Image(base, S, t) = f
            BY <1>2 DEF Image, BulkP, f
        <2>2. DOMAIN f = DOMAIN base
            BY DomCtor DEF f
        <2>3. \A k \in DOMAIN base :
                f[k] = (IF k \in S THEN P!Project(base[k], t) ELSE base[k])
            BY Zenon DEF f
        <2>4. f = [ i \in DOMAIN f |-> f[i] ]
            BY <2>2, <2>3, ExtCtor DEF f
        <2>5. QED
            BY <2>1, <2>4
    <1>3. QED
        BY <1>1, <1>2

LEMMA SliceAgree ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW S,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t }
    PROVE  /\ DOMAIN Image(doc, S, t)
              = { i \in DOMAIN Image(base, S, t) : i.origin = o }
           /\ \A k \in DOMAIN Image(doc, S, t) :
                 Image(base, S, t)[k] = Image(doc, S, t)[k]
PROOF
    <1>1. S \subseteq DOMAIN doc /\ DOMAIN doc \subseteq DOMAIN base
        BY Zenon
    <1>2. S \subseteq DOMAIN base
        BY <1>1, Zenon
    <1>3. DOMAIN Image(doc, S, t) = DOMAIN doc
        BY <1>1, ImageDom
    <1>4. DOMAIN Image(base, S, t) = DOMAIN base
        BY <1>2, ImageDom
    <1>5. DOMAIN Image(doc, S, t)
            = { i \in DOMAIN Image(base, S, t) : i.origin = o }
        BY <1>3, <1>4, Zenon
    <1>6. ASSUME NEW k \in DOMAIN Image(doc, S, t)
          PROVE  Image(base, S, t)[k] = Image(doc, S, t)[k]
        <2>1. k \in DOMAIN doc /\ k \in DOMAIN base
            BY <1>3, <1>4, <1>6, Zenon
        <2>2. base[k] = doc[k]
            BY <2>1, Zenon
        <2>3. Image(doc, S, t)[k]
                = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
            BY <1>1, <2>1, ImageVal
        <2>4. Image(base, S, t)[k]
                = IF k \in S THEN P!Project(base[k], t) ELSE base[k]
            BY <1>2, <2>1, ImageVal
        <2>5. P!Project(base[k], t) = P!Project(doc[k], t)
            BY <2>2, Zenon
        <2>6. QED
            BY <2>2, <2>3, <2>4, <2>5, Z3
    <1>7. QED
        BY <1>5, <1>6

LEMMA SlicePt ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW S, NEW k,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t },
           k \in DOMAIN Image(doc, S, t)
    PROVE  Image(base, S, t)[k] = Image(doc, S, t)[k]
PROOF
    <1>1. S \subseteq DOMAIN doc /\ DOMAIN doc \subseteq DOMAIN base
        BY Zenon
    <1>2. S \subseteq DOMAIN base
        BY <1>1, Zenon
    <1>3. DOMAIN Image(doc, S, t) = DOMAIN doc
        BY <1>1, ImageDom
    <1>4. DOMAIN Image(base, S, t) = DOMAIN base
        BY <1>2, ImageDom
    <1>5. k \in DOMAIN doc /\ k \in DOMAIN base
        BY <1>3, <1>4, Zenon
    <1>6. base[k] = doc[k]
        BY <1>5, Zenon
    <1>7. Image(doc, S, t)[k]
            = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
        BY <1>1, <1>5, ImageVal
    <1>8. Image(base, S, t)[k]
            = IF k \in S THEN P!Project(base[k], t) ELSE base[k]
        BY <1>2, <1>5, ImageVal
    <1>9. P!Project(base[k], t) = P!Project(doc[k], t)
        BY <1>6, Zenon
    <1>10. QED
        BY <1>6, <1>7, <1>8, <1>9, Z3

LEMMA SliceDom ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW S,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t }
    PROVE  DOMAIN Image(doc, S, t)
              = { i \in DOMAIN Image(base, S, t) : i.origin = o }
PROOF
    <1>1. S \subseteq DOMAIN doc /\ DOMAIN doc \subseteq DOMAIN base
        BY Zenon
    <1>2. S \subseteq DOMAIN base
        BY <1>1, Zenon
    <1>3. DOMAIN Image(doc, S, t) = DOMAIN doc
        BY <1>1, ImageDom
    <1>4. DOMAIN Image(base, S, t) = DOMAIN base
        BY <1>2, ImageDom
    <1>5. QED
        BY <1>3, <1>4, Zenon

LEMMA InDue ==
    ASSUME NEW o, NEW t, NEW p
    PROVE  p \in DueN(o, t)
            <=> /\ p \in [id : { q \in DOMAIN o :
                                   P!Project(o[q], t).promise.state /= "pending" },
                          address : Address]
                /\ p.address \in o[p.id].promise.listeners
PROOF
    BY ONLY Zenon DEF DueN, Ids

LEMMA PairsSub ==
    ASSUME NEW base, NEW doc, NEW t,
           DOMAIN doc \subseteq DOMAIN base,
           \A k \in DOMAIN doc : base[k] = doc[k]
    PROVE  DueN(doc, t) \subseteq DueN(base, t)
PROOF
    <1>1. ASSUME NEW p \in DueN(doc, t)
          PROVE  p \in DueN(base, t)
        <2> DEFINE ids ==
                { q \in DOMAIN doc :
                    P!Project(doc[q], t).promise.state /= "pending" }
        <2>1. /\ p \in [id : ids, address : Address]
              /\ p.address \in doc[p.id].promise.listeners
            BY <1>1, InDue DEF ids
        <2>2. p.id \in ids /\ p.address \in Address
            BY <2>1, Z3
        <2>3. p.id \in DOMAIN doc /\ base[p.id] = doc[p.id]
            BY <2>2, Zenon DEF ids
        <2>4. p.id \in DOMAIN base
            BY <2>3, Zenon
        <2>5. P!Project(base[p.id], t) = P!Project(doc[p.id], t)
            BY <2>3, Zenon
        <2>6. p.id \in { q \in DOMAIN base :
                           P!Project(base[q], t).promise.state /= "pending" }
            BY <2>2, <2>4, <2>5, Zenon DEF ids
        <2>7. p = [id |-> p.id, address |-> p.address]
            BY <2>1, RecPair
        <2>8. p \in [id : { q \in DOMAIN base :
                              P!Project(base[q], t).promise.state /= "pending" },
                     address : Address]
              /\ p.address \in base[p.id].promise.listeners
            BY <2>1, <2>3, <2>6, <2>7, Zenon
        <2>9. QED
            BY <2>8, InDue
    <1>2. QED
        BY <1>1

LEMMA FixedAt ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW S,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t }
    PROVE  \A k \in DOMAIN Image(doc, S, t) :
              P!Project(Image(base, S, t)[k], t) = Image(base, S, t)[k]
PROOF
    <1>1. S \subseteq DOMAIN doc
        BY Zenon
    <1>2. ASSUME NEW k \in DOMAIN Image(doc, S, t)
          PROVE  P!Project(Image(base, S, t)[k], t) = Image(base, S, t)[k]
        <2>1. k \in DOMAIN doc
            BY <1>1, <1>2, ImageDom, Zenon
        <2>2. S \subseteq DOMAIN base /\ k \in DOMAIN base
            BY <1>1, <2>1, Zenon
        <2>3. base[k] = doc[k]
            BY <2>1, Zenon
        <2>4. Image(doc, S, t)[k]
                = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
            BY <1>1, <2>1, ImageVal
        <2>5. Image(base, S, t)[k]
                = IF k \in S THEN P!Project(base[k], t) ELSE base[k]
            BY <2>1, <2>2, ImageVal
        <2>6. P!Project(base[k], t) = P!Project(doc[k], t)
            BY <2>3, Zenon
        <2>7. Image(base, S, t)[k] = Image(doc, S, t)[k]
            BY <2>3, <2>4, <2>5, <2>6, Z3
        <2>8. P!Project(Image(doc, S, t)[k], t) = Image(doc, S, t)[k]
            BY <2>1, SliceFixed
        <2>9. QED
            BY <2>7, <2>8, Z3
    <1>3. QED
        BY <1>2

LEMMA ReachSame ==
    ASSUME NEW base, NEW box, NEW t, NEW os, NEW os2, NEW b, NEW n,
           ReachN(base, box, t, os, b, n),
           os = os2
    PROVE  ReachN(base, box, t, os2, b, n)
PROOF
    <1>1. \E chain :
            /\ chain[0] = Store(base, box)
            /\ StepOk(chain, t, n)
            /\ chain[n] = Store(os, b)
        BY DEF ReachN
    <1>2. Store(os, b) = Store(os2, b)
        BY Z3 DEF Store
    <1>3. QED
        BY <1>1, <1>2, Zenon DEF ReachN

(* Listener pairs of the timeout image are due in the planted store, so
   the listener pass is a chain from that store. *)
LEMMA ListenFrom ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW box, NEW S,
           DOMAIN base \subseteq Id,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           base = [ i \in DOMAIN base |-> base[i] ],
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t },
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address
    PROVE  ReachN(Image(base, S, t), box, t,
                  ImgN(Image(base, S, t), DueN(Image(doc, S, t), t)),
                  BoxN(box, Image(base, S, t), DueN(Image(doc, S, t), t), t),
                  Cardinality(DueN(Image(doc, S, t), t)))
PROOF
    <1> DEFINE imB == Image(base, S, t)
    <1> DEFINE imD == Image(doc, S, t)
    <1> DEFINE pairs == DueN(imD, t)
    <1>1. S \subseteq DOMAIN doc
        BY Zenon
    <1>2. DOMAIN doc \subseteq DOMAIN base /\ S \subseteq DOMAIN base
        BY <1>1, Zenon
    <1>3. DOMAIN imD = DOMAIN doc /\ DOMAIN imB = DOMAIN base
        BY <1>1, <1>2, ImageDom DEF imD, imB
    <1>4. DOMAIN imD \subseteq Id /\ DOMAIN imB \subseteq Id
        BY <1>2, <1>3, Zenon
    <1>5. IsFiniteSet(pairs)
        BY <1>4, PairFinite DEF pairs, imD
    <1>6. ASSUME NEW k \in DOMAIN imD
          PROVE  imB[k] = imD[k]
        <2>1. k \in DOMAIN Image(doc, S, t)
            BY DEF imD
        <2>2. S \subseteq DOMAIN doc /\ DOMAIN doc \subseteq DOMAIN base
            BY Zenon
        <2>3. S \subseteq DOMAIN base /\ DOMAIN Image(doc, S, t) = DOMAIN doc
            BY <2>2, ImageDom
        <2>4. k \in DOMAIN doc /\ k \in DOMAIN base
            BY <2>1, <2>2, <2>3, Zenon
        <2>5. base[k] = doc[k]
            BY <2>4, Zenon
        <2>6. Image(doc, S, t)[k]
                = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
            BY <2>2, <2>4, ImageVal
        <2>7. Image(base, S, t)[k]
                = IF k \in S THEN P!Project(base[k], t) ELSE base[k]
            BY <2>3, <2>4, ImageVal
        <2>8. P!Project(base[k], t) = P!Project(doc[k], t)
            BY <2>5, Zenon
        <2>9. Image(base, S, t)[k] = Image(doc, S, t)[k]
            BY <2>5, <2>6, <2>7, <2>8, Z3
        <2>10. QED
            BY <2>9 DEF imB, imD
    <1>7. DOMAIN imD \subseteq DOMAIN imB
        BY <1>2, <1>3, Zenon
    <1>8. pairs \subseteq DueN(imB, t)
        BY <1>6, <1>7, PairsSub DEF pairs, imD, imB
    <1>9. \A y \in pairs : P!Project(imB[y.id], t) = imB[y.id]
        <2> SUFFICES ASSUME NEW y \in pairs
                     PROVE  P!Project(imB[y.id], t) = imB[y.id]
            OBVIOUS
        <2>1. y \in [id : DOMAIN imD, address : Address]
            BY PairSubset DEF pairs, imD
        <2>2. y.id \in DOMAIN imD
            BY <2>1, Z3
        <2>3. y.id \in DOMAIN doc
            BY <1>3, <2>2
        <2>4. \A j \in DOMAIN Image(doc, S, t) :
                P!Project(Image(base, S, t)[j], t) = Image(base, S, t)[j]
            BY FixedAt
        <2>5. QED
            BY <2>2, <2>4, Z3 DEF imB, imD
    <1>10. QED
        BY <1>4, <1>5, <1>8, <1>9, ListenOn DEF pairs, imB

LEMMA ListenPlant ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW S,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           base = [ i \in DOMAIN base |-> base[i] ],
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t },
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address
    PROVE  Plant(Image(base, S, t), o, SweepListeners(Image(doc, S, t), t).doc)
              = ImgN(Image(base, S, t), DueN(Image(doc, S, t), t))
PROOF
    <1> DEFINE imB == Image(base, S, t)
    <1> DEFINE imD == Image(doc, S, t)
    <1> DEFINE pairs == DueN(imD, t)
    <1>1. S \subseteq DOMAIN doc
        BY Zenon
    <1>2. S \subseteq DOMAIN base
        BY <1>1, Zenon
    <1>3. SweepListeners(imD, t).doc = ImgN(imD, pairs)
        BY ListenAfter DEF imD, pairs
    <1>4. imB = [ i \in DOMAIN imB |-> imB[i] ]
        BY <1>2, EtaImage DEF imB
    <1>5. DOMAIN imD = { i \in DOMAIN imB : i.origin = o }
        BY SliceDom DEF imB, imD
    <1>5b. ASSUME NEW k \in DOMAIN imD
           PROVE  imB[k] = imD[k]
        <2>1. k \in DOMAIN Image(doc, S, t)
            BY DEF imD
        <2>2. S \subseteq DOMAIN doc /\ DOMAIN doc \subseteq DOMAIN base
            BY Zenon
        <2>3. S \subseteq DOMAIN base /\ DOMAIN Image(doc, S, t) = DOMAIN doc
            BY <2>2, ImageDom
        <2>4. k \in DOMAIN doc /\ k \in DOMAIN base
            BY <2>1, <2>2, <2>3, Zenon
        <2>5. base[k] = doc[k]
            BY <2>4, Zenon
        <2>6. Image(doc, S, t)[k]
                = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
            BY <2>2, <2>4, ImageVal
        <2>7. Image(base, S, t)[k]
                = IF k \in S THEN P!Project(base[k], t) ELSE base[k]
            BY <2>3, <2>4, ImageVal
        <2>8. P!Project(base[k], t) = P!Project(doc[k], t)
            BY <2>5, Zenon
        <2>9. Image(base, S, t)[k] = Image(doc, S, t)[k]
            BY <2>5, <2>6, <2>7, <2>8, Z3
        <2>10. QED
            BY <2>9 DEF imB, imD
    <1>6. pairs \subseteq [id : DOMAIN imD, address : Address]
        BY PairSubset DEF pairs, imD
    <1>7. Plant(imB, o, ImgN(imD, pairs)) = ImgN(imB, pairs)
        BY <1>4, <1>5, <1>5b, <1>6, PlantN DEF imB, imD, pairs
    <1>8. QED
        BY <1>3, <1>7 DEF imB, pairs

LEMMA TwoPass ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW box, NEW S,
           DOMAIN base \subseteq Id,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           base = [ i \in DOMAIN base |-> base[i] ],
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t },
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address
    PROVE  ReachN(base, box, t,
                  ImgN(Image(base, S, t), DueN(Image(doc, S, t), t)),
                  BoxN(box, Image(base, S, t), DueN(Image(doc, S, t), t), t),
                  Cardinality(S) + Cardinality(DueN(Image(doc, S, t), t)))
PROOF
    <1> DEFINE imB == Image(base, S, t)
    <1> DEFINE imD == Image(doc, S, t)
    <1> DEFINE pairs == DueN(imD, t)
    <1>1. /\ ReachN(base, box, t,
                    Plant(base, o, SweepTimeoutAt(doc, t).doc),
                    box, Cardinality(S))
          /\ Cardinality(S) \in 0 .. P!MaxSweep
        BY TimeoutChain
    <1>2. Plant(base, o, SweepTimeoutAt(doc, t).doc) = imB
        BY TimeoutPlant DEF imB
    <1>3. ReachN(base, box, t, imB, box, Cardinality(S))
        BY <1>1, <1>2, ReachSame DEF imB
    <1>4. ReachN(imB, box, t,
                 ImgN(imB, pairs),
                 BoxN(box, imB, pairs, t),
                 Cardinality(pairs))
        BY ListenFrom DEF imB, imD, pairs
    <1>5. IsFiniteSet(pairs)
        <2>1. S \subseteq DOMAIN doc /\ DOMAIN doc \subseteq DOMAIN base
            BY Zenon
        <2>2. DOMAIN imD = DOMAIN doc
            BY <2>1, ImageDom DEF imD
        <2>3. DOMAIN imD \subseteq Id
            BY <2>1, <2>2, Zenon
        <2>4. QED
            BY <2>3, PairFinite DEF pairs, imD
    <1>6. Cardinality(S) \in Nat /\ Cardinality(pairs) \in Nat
        <2>1. P!MaxSweep \in Nat
            BY SweepCap
        <2>2. Cardinality(S) \in Nat
            BY <1>1, <2>1, Z3
        <2>3. Cardinality(pairs) \in Nat
            BY <1>5, FS_CardinalityType DEF pairs
        <2>4. QED
            BY <2>2, <2>3
    <1>7. QED
        BY <1>3, <1>4, <1>6, ReachCat DEF imB, pairs

(* Dropping listeners does not disturb a projection that is already the
   identity, so the callback pass can start from the listener image. *)
LEMMA StillFixed ==
    ASSUME NEW doc, NEW t, NEW Q, NEW k, NEW obj,
           k \in DOMAIN doc,
           obj = doc[k],
           P!Project(obj, t) = obj
    PROVE  /\ k \in DOMAIN ImgN(doc, Q)
           /\ P!Project(ImgN(doc, Q)[k], t) = ImgN(doc, Q)[k]
PROOF
    <1>0. P!Project(doc[k], t) = doc[k]
        BY Zenon
    <1>1. CASE Q = {}
        <2>1. ImgN(doc, Q) = doc
            BY <1>1 DEF ImgN
        <2>2. QED
            BY <1>0, <2>1, Zenon
    <1>2. CASE Q # {}
        <2> DEFINE im == [ j \in DOMAIN doc |-> BodyN(doc, Q, j) ]
        <2>1. ImgN(doc, Q) = im
            BY <1>2 DEF ImgN, im
        <2>2. DOMAIN im = DOMAIN doc
            BY DomCtor DEF im
        <2>3. im[k] = BodyN(doc, Q, k)
            BY Zenon DEF im
        <2>4. CASE Gone(k, Q) = {}
            <3>1. BodyN(doc, Q, k)
                    = (LET g == Gone(k, Q)
                       IN  IF g = {} THEN doc[k] ELSE Struck(doc[k], g))
                BY BodyWhen
            <3>2. BodyN(doc, Q, k) = doc[k]
                BY ONLY <2>4, <3>1, Zenon
            <3>3. QED
                BY <1>0, <2>1, <2>2, <2>3, <3>2, Zenon
        <2>5. CASE Gone(k, Q) # {}
            <3>1. BodyN(doc, Q, k)
                    = (LET g == Gone(k, Q)
                       IN  IF g = {} THEN doc[k] ELSE Struck(doc[k], g))
                BY BodyWhen
            <3>2. BodyN(doc, Q, k) = Struck(doc[k], Gone(k, Q))
                BY ONLY <2>5, <3>1, Zenon
            <3>3. P!Project(Struck(doc[k], Gone(k, Q)), t)
                    = Struck(doc[k], Gone(k, Q))
                BY <1>0, ProjectDrop
            <3>4. QED
                BY <2>1, <2>2, <2>3, <3>2, <3>3, Zenon
        <2>6. QED
            BY <2>4, <2>5
    <1>3. QED
        BY <1>1, <1>2

(* Listeners do not touch callbacks, so the callback pass of the listener
   image is the abstract callback image of that same document. *)
LEMMA CallAfter ==
    ASSUME NEW doc, NEW t, NEW Q,
           \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id,
           \A k \in DOMAIN doc : P!Project(doc[k], t) = doc[k]
    PROVE  SweepCallbacks(ImgN(doc, Q), t).doc
              = ImgC(ImgN(doc, Q), DueC(ImgN(doc, Q), t), t)
PROOF
    <1> DEFINE im == ImgN(doc, Q)
    <1>1. ASSUME NEW k \in DOMAIN im
          PROVE  im[k].promise.callbacks \subseteq Id
        <2>1. CASE Q = {}
            <3>1. im = doc
                BY <2>1 DEF im, ImgN
            <3>2. k \in DOMAIN doc /\ im[k] = doc[k]
                BY <1>1, <3>1
            <3>3. QED
                BY <3>2
        <2>2. CASE Q # {}
            <3> DEFINE body == [ j \in DOMAIN doc |-> BodyN(doc, Q, j) ]
            <3>1. im = body /\ DOMAIN body = DOMAIN doc
                BY <2>2, DomCtor DEF im, ImgN, body
            <3>2. k \in DOMAIN doc /\ body[k] = BodyN(doc, Q, k)
                BY <1>1, <3>1, Zenon DEF body
            <3>3. doc[k].promise.callbacks \subseteq Id
                BY <3>2
            <3>4. CASE Gone(k, Q) = {}
                <4>1. BodyN(doc, Q, k)
                        = (LET g == Gone(k, Q)
                           IN  IF g = {} THEN doc[k] ELSE Struck(doc[k], g))
                    BY BodyWhen
                <4>2. BodyN(doc, Q, k) = doc[k]
                    BY ONLY <3>4, <4>1, Zenon
                <4>3. QED
                    BY <3>1, <3>2, <3>3, <4>2
            <3>5. CASE Gone(k, Q) # {}
                <4> DEFINE s == Struck(doc[k], Gone(k, Q))
                <4>1. BodyN(doc, Q, k)
                        = (LET g == Gone(k, Q)
                           IN  IF g = {} THEN doc[k] ELSE Struck(doc[k], g))
                    BY BodyWhen
                <4>2. BodyN(doc, Q, k) = s
                    BY ONLY <3>5, <4>1, Zenon DEF s
                <4>3. s.promise.callbacks = doc[k].promise.callbacks
                    BY ONLY Zenon DEF s, Struck
                <4>4. QED
                    BY <3>1, <3>2, <3>3, <4>2, <4>3
            <3>6. QED
                BY <3>4, <3>5
        <2>3. QED
            BY <2>1, <2>2
    <1>2. ASSUME NEW k \in DOMAIN im
          PROVE  P!Project(im[k], t) = im[k]
        <2>1. CASE Q = {}
            <3>1. im = doc
                BY <2>1 DEF im, ImgN
            <3>2. k \in DOMAIN doc /\ im[k] = doc[k]
                BY <1>2, <3>1
            <3>3. QED
                BY <3>2
        <2>2. CASE Q # {}
            <3> DEFINE body == [ j \in DOMAIN doc |-> BodyN(doc, Q, j) ]
            <3>1. im = body /\ DOMAIN body = DOMAIN doc
                BY <2>2, DomCtor DEF im, ImgN, body
            <3>2. k \in DOMAIN doc /\ im[k] = BodyN(doc, Q, k)
                BY <1>2, <3>1, Zenon DEF body, im
            <3>3. P!Project(doc[k], t) = doc[k]
                BY <3>2
            <3>4. CASE Gone(k, Q) = {}
                <4>1. BodyN(doc, Q, k)
                        = (LET g == Gone(k, Q)
                           IN  IF g = {} THEN doc[k] ELSE Struck(doc[k], g))
                    BY BodyWhen
                <4>2. BodyN(doc, Q, k) = doc[k]
                    BY ONLY <3>4, <4>1, Zenon
                <4>3. QED
                    BY <3>2, <3>3, <4>2
            <3>5. CASE Gone(k, Q) # {}
                <4> DEFINE s == Struck(doc[k], Gone(k, Q))
                <4>1. BodyN(doc, Q, k)
                        = (LET g == Gone(k, Q)
                           IN  IF g = {} THEN doc[k] ELSE Struck(doc[k], g))
                    BY BodyWhen
                <4>2. BodyN(doc, Q, k) = s
                    BY ONLY <3>5, <4>1, Zenon DEF s
                <4>3. P!Project(s, t) = s
                    BY <3>3, ProjectDrop DEF s
                <4>4. QED
                    BY <3>2, <4>2, <4>3
            <3>6. QED
                BY <3>4, <3>5
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2, CallDoc DEF im

LEMMA SameBodyC ==
    ASSUME NEW a, NEW b, NEW S, NEW j, NEW t, a[j] = b[j]
    PROVE  BodyC(a, S, j, t) = BodyC(b, S, j, t)
PROOF
    <1> DEFINE g == Drp(j, S)
    <1> DEFINE sa == Src(j, S)
    <1>1. Cleared(a, S, j)
            = (IF g = {} THEN a[j] ELSE P!WithoutCallbacks(a[j], g))
        BY DEF Cleared, g
    <1>2. Cleared(b, S, j)
            = (IF g = {} THEN b[j] ELSE P!WithoutCallbacks(b[j], g))
        BY DEF Cleared, g
    <1>3. Cleared(a, S, j) = Cleared(b, S, j)
        BY <1>1, <1>2, Z3
    <1>4. BodyC(a, S, j, t) = Woken(Cleared(a, S, j), sa, t)
        BY DEF BodyC, sa
    <1>5. BodyC(b, S, j, t) = Woken(Cleared(b, S, j), sa, t)
        BY DEF BodyC, sa
    <1>6. Woken(Cleared(a, S, j), sa, t) = Woken(Cleared(b, S, j), sa, t)
        BY <1>3, Z3 DEF Woken
    <1>7. QED
        BY <1>4, <1>5, <1>6

LEMMA SrcOut ==
    ASSUME NEW j, NEW S, \A y \in S : y.awaiter /= j
    PROVE  Src(j, S) = {}
PROOF
    <1>1. Src(j, S) = { p.id : p \in { y \in S : y.awaiter = j } }
        BY DEF Src
    <1>2. { y \in S : y.awaiter = j } = {}
        BY Zenon
    <1>3. { p.id : p \in {} } = {}
        BY Zenon
    <1>4. QED
        BY <1>1, <1>2, <1>3, Zenon

(* A callback image of one document, planted, is the callback image of the
   whole store when every awaiter that exists is in that document. *)
LEMMA PlantC ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW S,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           base = [ i \in DOMAIN base |-> base[i] ],
           S \subseteq [id : DOMAIN doc, awaiter : Id],
           \A y \in S : y.awaiter \in DOMAIN base => y.awaiter \in DOMAIN doc
    PROVE  Plant(base, o, ImgC(doc, S, t)) = ImgC(base, S, t)
PROOF
    <1>1. CASE S = {}
        <2>1. ImgC(doc, S, t) = doc /\ ImgC(base, S, t) = base
            BY <1>1 DEF ImgC
        <2>2. Plant(base, o, doc) = base
            BY PlantId
        <2>3. QED
            BY <2>1, <2>2
    <1>2. CASE S # {}
        <2> DEFINE body == [ j \in DOMAIN doc |-> BodyC(doc, S, j, t) ]
        <2> DEFINE full == [ j \in DOMAIN base |-> BodyC(base, S, j, t) ]
        <2>1. ImgC(doc, S, t) = body
            BY <1>2 DEF ImgC, body
        <2>2. ImgC(base, S, t) = full
            BY <1>2 DEF ImgC, full
        <2>3. DOMAIN body = DOMAIN doc
            BY DomCtor DEF body
        <2> DEFINE kept == { q \in DOMAIN base : q.origin /= o }
        <2> DEFINE dom == kept \cup DOMAIN body
        <2>4. \A n : n \in dom <=> n \in DOMAIN base
            BY <2>3 DEF kept, dom
        <2>5. dom = DOMAIN base
            BY <2>4, SetExtensionality DEF dom
        <2>6. \A n \in DOMAIN base :
                (IF n \in DOMAIN body THEN body[n] ELSE base[n]) = full[n]
            <3> SUFFICES ASSUME NEW k \in DOMAIN base
                         PROVE  (IF k \in DOMAIN body THEN body[k] ELSE base[k])
                                  = full[k]
                OBVIOUS
            <3>1. full[k] = BodyC(base, S, k, t)
                BY Zenon DEF full
            <3>2. CASE k \in DOMAIN doc
                <4>1. k \in DOMAIN body /\ body[k] = BodyC(doc, S, k, t)
                    BY <2>3, <3>2, Zenon DEF body
                <4>2. base[k] = doc[k]
                    BY <3>2, Zenon
                <4>3. BodyC(base, S, k, t) = BodyC(doc, S, k, t)
                    BY <4>2, SameBodyC
                <4>4. QED
                    BY <3>1, <4>1, <4>3
            <3>3. CASE k \notin DOMAIN doc
                <4>1. k \notin DOMAIN body
                    BY <2>3, <3>3
                <4>2. \A y \in S : y.awaiter /= k
                    BY <3>3, Zenon
                <4>3. Src(k, S) = {}
                    BY <4>2, SrcOut
                <4>4. Cleared(base, S, k) = base[k]
                    <5> DEFINE g == Drp(k, S)
                    <5>1. CASE g = {}
                        BY <5>1 DEF Cleared, g
                    <5>2. CASE g # {}
                        <6>1. \E y \in S : y.id = k
                            BY <5>2 DEF Drp, g
                        <6>2. PICK y \in S : y.id = k
                            BY <6>1
                        <6>3. y \in [id : DOMAIN doc, awaiter : Id]
                            BY <6>2
                        <6>4. y.id \in DOMAIN doc
                            BY <6>3, Z3
                        <6>5. FALSE
                            BY <3>3, <6>2, <6>4
                        <6>6. QED
                            BY <6>5
                    <5>3. QED
                        BY <5>1, <5>2
                <4>5. Woken(base[k], {}, t) = base[k]
                    BY DEF Woken
                <4>6. BodyC(base, S, k, t)
                        = Woken(Cleared(base, S, k), Src(k, S), t)
                    BY DEF BodyC
                <4>7. BodyC(base, S, k, t) = base[k]
                    BY <4>3, <4>4, <4>5, <4>6, Zenon
                <4>8. QED
                    BY <3>1, <4>1, <4>7
            <3>4. QED
                BY <3>2, <3>3
        <2>7. Plant(base, o, body)
                = [ n \in dom |-> IF n \in DOMAIN body THEN body[n] ELSE base[n] ]
            BY DEF Plant, kept, dom
        <2>8. [ n \in dom |-> IF n \in DOMAIN body THEN body[n] ELSE base[n] ]
                = full
            BY <2>5, <2>6, ExtCtor DEF full
        <2>9. QED
            BY <2>1, <2>2, <2>7, <2>8
    <1>3. QED
        BY <1>1, <1>2

LEMMA AwSub ==
    ASSUME NEW o, NEW t
    PROVE  DueC(o, t) \subseteq [id : DOMAIN o, awaiter : Id]
PROOF
    BY DEF DueC, IdsC

LEMMA InDueC ==
    ASSUME NEW o, NEW t, NEW p
    PROVE  p \in DueC(o, t)
            <=> /\ p \in [id : { q \in DOMAIN o :
                                   P!Project(o[q], t).promise.state /= "pending" },
                          awaiter : Id]
                /\ p.awaiter \in o[p.id].promise.callbacks
PROOF
    BY ONLY Zenon DEF DueC, IdsC

(* A document that agrees with the store has no extra due callbacks. *)
LEMMA CallsSub ==
    ASSUME NEW base, NEW doc, NEW t,
           DOMAIN doc \subseteq DOMAIN base,
           \A k \in DOMAIN doc : base[k] = doc[k]
    PROVE  DueC(doc, t) \subseteq DueC(base, t)
PROOF
    <1>1. ASSUME NEW p \in DueC(doc, t)
          PROVE  p \in DueC(base, t)
        <2> DEFINE ids ==
                { q \in DOMAIN doc :
                    P!Project(doc[q], t).promise.state /= "pending" }
        <2>1. /\ p \in [id : ids, awaiter : Id]
              /\ p.awaiter \in doc[p.id].promise.callbacks
            BY <1>1, InDueC DEF ids
        <2>2. p.id \in ids /\ p.awaiter \in Id
            BY <2>1, Z3
        <2>3. p.id \in DOMAIN doc /\ base[p.id] = doc[p.id]
            BY <2>2, Zenon DEF ids
        <2>4. p.id \in DOMAIN base
            BY <2>3, Zenon
        <2>5. P!Project(base[p.id], t) = P!Project(doc[p.id], t)
            BY <2>3, Zenon
        <2>6. p.id \in { q \in DOMAIN base :
                           P!Project(base[q], t).promise.state /= "pending" }
            BY <2>2, <2>4, <2>5, Zenon DEF ids
        <2>7. p = [id |-> p.id, awaiter |-> p.awaiter]
            BY <2>1, RecAw
        <2>8. p \in [id : { q \in DOMAIN base :
                              P!Project(base[q], t).promise.state /= "pending" },
                     awaiter : Id]
              /\ p.awaiter \in base[p.id].promise.callbacks
            BY <2>1, <2>3, <2>6, <2>7, Zenon
        <2>9. QED
            BY <2>8, InDueC
    <1>2. QED
        BY <1>1

LEMMA LocalDue ==
    ASSUME NEW base, NEW doc, NEW t,
           \A y \in [id : DOMAIN doc, awaiter : Id] :
               y.awaiter \in DOMAIN base => y.awaiter \in DOMAIN doc
    PROVE  \A y \in DueC(doc, t) :
               y.awaiter \in DOMAIN base => y.awaiter \in DOMAIN doc
PROOF
    <1>1. DueC(doc, t) \subseteq [id : DOMAIN doc, awaiter : Id]
        BY AwSub
    <1>2. ASSUME NEW y \in DueC(doc, t), y.awaiter \in DOMAIN base
          PROVE  y.awaiter \in DOMAIN doc
        <2>1. y \in [id : DOMAIN doc, awaiter : Id]
            BY <1>1, <1>2, Zenon
        <2>2. QED
            BY <2>1, <1>2, Zenon
    <1>3. QED
        BY <1>2

(* Due callbacks of one document are a chain in the whole store when that
   document is a projected slice and every existing awaiter lives there.
   The outbox is unchanged. *)
LEMMA CallFrom ==
    ASSUME NEW base, NEW doc, NEW t, NEW box,
           DOMAIN base \subseteq Id,
           DOMAIN doc \subseteq DOMAIN base,
           \A k \in DOMAIN doc : base[k] = doc[k],
           \A k \in DOMAIN doc : P!Project(doc[k], t) = doc[k],
           \A y \in DueC(doc, t) :
               y.awaiter \in DOMAIN base => y.awaiter \in DOMAIN doc
    PROVE  ReachN(base, box, t,
                  ImgC(base, DueC(doc, t), t),
                  box,
                  Cardinality(DueC(doc, t)))
PROOF
    <1> DEFINE calls == DueC(doc, t)
    <1>1. DOMAIN doc \subseteq Id
        BY Zenon
    <1>2. IsFiniteSet(calls)
        BY <1>1, AwFinite DEF calls
    <1>3. calls \subseteq DueC(base, t)
        BY CallsSub DEF calls
    <1>4. \A y \in calls : P!Project(base[y.id], t) = base[y.id]
        <2> SUFFICES ASSUME NEW y \in calls
                     PROVE  P!Project(base[y.id], t) = base[y.id]
            OBVIOUS
        <2>1. y \in [id : DOMAIN doc, awaiter : Id]
            BY AwSub DEF calls
        <2>2. y.id \in DOMAIN doc
            BY <2>1, Z3
        <2>3. base[y.id] = doc[y.id]
            BY <2>2, Zenon
        <2>4. P!Project(doc[y.id], t) = doc[y.id]
            BY <2>2
        <2>5. QED
            BY <2>3, <2>4, Zenon
    <1>5. \A y \in calls :
            y.awaiter \in DOMAIN base =>
                P!Project(base[y.awaiter], t) = base[y.awaiter]
        <2> SUFFICES ASSUME NEW y \in calls, y.awaiter \in DOMAIN base
                     PROVE  P!Project(base[y.awaiter], t) = base[y.awaiter]
            OBVIOUS
        <2>1. y.awaiter \in DOMAIN doc
            BY DEF calls
        <2>2. base[y.awaiter] = doc[y.awaiter]
            BY <2>1, Zenon
        <2>3. P!Project(doc[y.awaiter], t) = doc[y.awaiter]
            BY <2>1
        <2>4. QED
            BY <2>2, <2>3, Zenon
    <1>6. QED
        BY <1>2, <1>3, <1>4, <1>5, CallOn DEF calls

(* Timeouts, listeners, and callbacks of one origin are one chain. The
   callback pass leaves the listener outbox where the listener pass put it.
   Awaiters that exist are still in the document. *)
LEMMA ThreePass ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW box, NEW S,
           DOMAIN base \subseteq Id,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           base = [ i \in DOMAIN base |-> base[i] ],
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t },
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address,
           \A y \in [id : DOMAIN doc, awaiter : Id] :
               y.awaiter \in DOMAIN base => y.awaiter \in DOMAIN doc
    PROVE  ReachN(base, box, t,
                  ImgC(ImgN(Image(base, S, t), DueN(Image(doc, S, t), t)),
                       DueC(ImgN(Image(doc, S, t),
                                 DueN(Image(doc, S, t), t)), t),
                       t),
                  BoxN(box, Image(base, S, t), DueN(Image(doc, S, t), t), t),
                  Cardinality(S)
                    + Cardinality(DueN(Image(doc, S, t), t))
                    + Cardinality(DueC(ImgN(Image(doc, S, t),
                                            DueN(Image(doc, S, t), t)), t)))
PROOF
    <1> DEFINE imB == Image(base, S, t)
    <1> DEFINE imD == Image(doc, S, t)
    <1> DEFINE pairs == DueN(imD, t)
    <1> DEFINE docL == ImgN(imD, pairs)
    <1> DEFINE mid == ImgN(imB, pairs)
    <1> DEFINE boxL == BoxN(box, imB, pairs, t)
    <1> DEFINE calls == DueC(docL, t)
    <1>1. S \subseteq DOMAIN doc /\ DOMAIN doc \subseteq DOMAIN base
        BY Zenon
    <1>2. S \subseteq DOMAIN base
        BY <1>1, Zenon
    <1>3. DOMAIN imD = DOMAIN doc /\ DOMAIN imB = DOMAIN base
        BY <1>1, <1>2, ImageDom DEF imD, imB
    <1>4. ASSUME NEW k \in DOMAIN imD
          PROVE  imB[k] = imD[k]
        <2>1. k \in DOMAIN doc /\ k \in DOMAIN base
            BY <1>3, <1>4, Zenon
        <2>2. base[k] = doc[k]
            BY <2>1, Zenon
        <2>3. imD[k] = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
            BY <1>1, <2>1, ImageVal DEF imD
        <2>4. imB[k] = IF k \in S THEN P!Project(base[k], t) ELSE base[k]
            BY <1>2, <2>1, ImageVal DEF imB
        <2>5. P!Project(base[k], t) = P!Project(doc[k], t)
            BY <2>2, Zenon
        <2>6. QED
            BY <2>2, <2>3, <2>4, <2>5, Z3
    <1>5. DOMAIN docL = DOMAIN imD /\ DOMAIN mid = DOMAIN imB
        <2>1. CASE pairs = {}
            <3>1. docL = imD /\ mid = imB
                BY <2>1 DEF docL, mid, ImgN
            <3>2. QED
                BY <3>1
        <2>2. CASE pairs # {}
            <3> DEFINE bD == [ j \in DOMAIN imD |-> BodyN(imD, pairs, j) ]
            <3> DEFINE bB == [ j \in DOMAIN imB |-> BodyN(imB, pairs, j) ]
            <3>1. docL = bD /\ mid = bB
                BY <2>2 DEF docL, mid, ImgN, bD, bB
            <3>2. DOMAIN bD = DOMAIN imD /\ DOMAIN bB = DOMAIN imB
                BY DomCtor DEF bD, bB
            <3>3. QED
                BY <3>1, <3>2
        <2>3. QED
            BY <2>1, <2>2
    <1>6. DOMAIN mid \subseteq Id /\ DOMAIN docL \subseteq DOMAIN mid
        BY <1>1, <1>3, <1>5, Zenon
    <1>7. \A k \in DOMAIN docL : mid[k] = docL[k]
        <2> SUFFICES ASSUME NEW k \in DOMAIN docL
                     PROVE  mid[k] = docL[k]
            OBVIOUS
        <2>1. k \in DOMAIN imD /\ k \in DOMAIN imB /\ imB[k] = imD[k]
            BY <1>1, <1>3, <1>4, <1>5, Zenon
        <2>2. CASE pairs = {}
            <3>1. docL = imD /\ mid = imB
                BY <2>2 DEF docL, mid, ImgN
            <3>2. QED
                BY <2>1, <3>1
        <2>3. CASE pairs # {}
            <3> DEFINE bD == [ j \in DOMAIN imD |-> BodyN(imD, pairs, j) ]
            <3> DEFINE bB == [ j \in DOMAIN imB |-> BodyN(imB, pairs, j) ]
            <3>1. docL = bD /\ mid = bB
                BY <2>3 DEF docL, mid, ImgN, bD, bB
            <3>2. bD[k] = BodyN(imD, pairs, k)
                BY <2>1, Zenon DEF bD
            <3>3. bB[k] = BodyN(imB, pairs, k)
                BY <2>1, Zenon DEF bB
            <3>4. BodyN(imB, pairs, k) = BodyN(imD, pairs, k)
                BY <2>1, SameBody
            <3>5. QED
                BY <3>1, <3>2, <3>3, <3>4
        <2>4. QED
            BY <2>2, <2>3
    <1>8. \A k \in DOMAIN imD : P!Project(imD[k], t) = imD[k]
        BY <1>3, SliceFixed DEF imD
    <1>9. \A k \in DOMAIN docL : P!Project(docL[k], t) = docL[k]
        <2> SUFFICES ASSUME NEW k \in DOMAIN docL
                     PROVE  P!Project(docL[k], t) = docL[k]
            OBVIOUS
        <2> DEFINE obj == imD[k]
        <2>1. k \in DOMAIN imD
            BY <1>5, Zenon
        <2>2. obj = imD[k] /\ P!Project(obj, t) = obj
            BY <1>8, <2>1, Zenon DEF obj
        <2>3. QED
            BY <2>1, <2>2, StillFixed DEF docL, pairs, obj
    <1>10. \A y \in [id : DOMAIN docL, awaiter : Id] :
              y.awaiter \in DOMAIN mid => y.awaiter \in DOMAIN docL
        <2> SUFFICES ASSUME NEW y \in [id : DOMAIN docL, awaiter : Id],
                            y.awaiter \in DOMAIN mid
                     PROVE  y.awaiter \in DOMAIN docL
            OBVIOUS
        <2>1. DOMAIN docL = DOMAIN doc /\ DOMAIN mid = DOMAIN base
            BY <1>3, <1>5, Zenon
        <2>2. y \in [id : DOMAIN doc, awaiter : Id]
            BY <2>1, Zenon
        <2>3. y.awaiter \in DOMAIN base
            BY <2>1, Zenon
        <2>4. y.awaiter \in DOMAIN doc
            BY <2>2, <2>3, Zenon
        <2>5. QED
            BY <2>1, <2>4, Zenon
    <1>11. \A y \in calls :
              y.awaiter \in DOMAIN mid => y.awaiter \in DOMAIN docL
        BY <1>10, LocalDue DEF calls, docL, mid
    <1>12. ReachN(mid, boxL, t, ImgC(mid, calls, t), boxL, Cardinality(calls))
        BY <1>6, <1>7, <1>9, <1>11, CallFrom DEF mid, docL, calls, boxL
    <1>13. ReachN(base, box, t, mid, boxL,
                  Cardinality(S) + Cardinality(pairs))
        BY TwoPass DEF imB, imD, pairs, mid, boxL
    <1>14. Cardinality(S) \in Nat
        <2>1. Cardinality(S) \in 0 .. P!MaxSweep
            BY TimeoutChain
        <2>2. P!MaxSweep \in Nat
            BY SweepCap
        <2>3. QED
            BY <2>1, <2>2, Z3
    <1>15. Cardinality(pairs) \in Nat
        <2>1. DOMAIN imD \subseteq Id
            BY <1>1, <1>3, Zenon
        <2>2. IsFiniteSet(pairs)
            BY <2>1, PairFinite DEF pairs, imD
        <2>3. QED
            BY <2>2, FS_CardinalityType
    <1>16. Cardinality(calls) \in Nat
        <2>1. DOMAIN docL \subseteq Id
            BY <1>6, Zenon
        <2>2. IsFiniteSet(calls)
            BY <2>1, AwFinite DEF calls, docL
        <2>3. QED
            BY <2>2, FS_CardinalityType
    <1>17. Cardinality(S) + Cardinality(pairs) \in Nat
        BY <1>14, <1>15, Z3
    <1>18. QED
        BY <1>12, <1>13, <1>16, <1>17, ReachCat DEF mid, boxL, calls

LEMMA CallsKept ==
    ASSUME NEW obj, NEW t
    PROVE  P!Project(obj, t).promise.callbacks = obj.promise.callbacks
PROOF
    <1>1. CASE obj.promise.state = "pending" /\ obj.promise.timeoutAt <= t
        <2> DEFINE p == P!Project(obj, t)
        <2> DEFINE st == IF obj.promise.tags.timer THEN "resolved"
                         ELSE "rejectedTimedout"
        <2> DEFINE p1 == [obj.promise EXCEPT !.state = st]
        <2> DEFINE p2 == [p1 EXCEPT !.value = NoValue]
        <2> DEFINE p3 == [p2 EXCEPT !.settledAt = obj.promise.timeoutAt]
        <2>1. p1.callbacks = obj.promise.callbacks
            BY ONLY Z3 DEF p1
        <2>2. p2.callbacks = p1.callbacks /\ p3.callbacks = p2.callbacks
            BY ONLY Z3 DEF p2, p3
        <2>3. p.promise = p3
            BY ONLY <1>1, Zenon DEF p, st, p1, p2, p3, P!Project
        <2>4. QED
            BY <2>1, <2>2, <2>3
    <1>2. CASE obj.promise.state /= "pending" \/ ~(obj.promise.timeoutAt <= t)
        BY <1>2, ProjectId
    <1>3. QED
        BY <1>1, <1>2

LEMMA CallsOn ==
    ASSUME NEW doc, NEW t, NEW S,
           S \subseteq DOMAIN doc,
           \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id
    PROVE  \A k \in DOMAIN Image(doc, S, t) :
              Image(doc, S, t)[k].promise.callbacks \subseteq Id
PROOF
    <1>1. DOMAIN Image(doc, S, t) = DOMAIN doc
        BY ImageDom
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  Image(doc, S, t)[k].promise.callbacks \subseteq Id
        <2>1. /\ k \in DOMAIN Image(doc, S, t)
              /\ Image(doc, S, t)[k]
                   = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
            BY <1>2, ImageVal
        <2>2. CASE k \in S
            <3>1. Image(doc, S, t)[k].promise.callbacks
                    = doc[k].promise.callbacks
                BY <2>1, <2>2, CallsKept
            <3>2. QED
                BY <1>2, <2>2, <3>1
        <2>3. CASE k \notin S
            BY <1>2, <2>1, <2>3
        <2>4. QED
            BY <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2

LEMMA EtaImgN ==
    ASSUME NEW base, NEW Q,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  ImgN(base, Q)
              = [ i \in DOMAIN ImgN(base, Q) |-> ImgN(base, Q)[i] ]
PROOF
    <1>1. CASE Q = {}
        <2>1. ImgN(base, Q) = base
            BY <1>1 DEF ImgN
        <2>2. DOMAIN ImgN(base, Q) = DOMAIN base
            BY <2>1
        <2>3. QED
            BY <2>1, <2>2, Zenon
    <1>2. CASE Q # {}
        <2> DEFINE f == [ j \in DOMAIN base |-> BodyN(base, Q, j) ]
        <2>1. ImgN(base, Q) = f
            BY <1>2 DEF ImgN, f
        <2>2. DOMAIN f = DOMAIN base
            BY DomCtor DEF f
        <2>3. \A k \in DOMAIN base : f[k] = BodyN(base, Q, k)
            BY Zenon DEF f
        <2>4. f = [ i \in DOMAIN f |-> f[i] ]
            BY <2>2, <2>3, ExtCtor DEF f
        <2>5. QED
            BY <2>1, <2>4
    <1>3. QED
        BY <1>1, <1>2

(* The concrete callback document, planted into the listener store, is the
   callback image that ThreePass reaches. *)
LEMMA CallPlant ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW S,
           DOMAIN base \subseteq Id,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           base = [ i \in DOMAIN base |-> base[i] ],
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t },
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address,
           \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id,
           \A y \in [id : DOMAIN doc, awaiter : Id] :
               y.awaiter \in DOMAIN base => y.awaiter \in DOMAIN doc
    PROVE  Plant(ImgN(Image(base, S, t), DueN(Image(doc, S, t), t)),
                 o,
                 SweepCallbacks(ImgN(Image(doc, S, t),
                                     DueN(Image(doc, S, t), t)), t).doc)
              = ImgC(ImgN(Image(base, S, t), DueN(Image(doc, S, t), t)),
                     DueC(ImgN(Image(doc, S, t),
                               DueN(Image(doc, S, t), t)), t),
                     t)
PROOF
    <1> DEFINE imB == Image(base, S, t)
    <1> DEFINE imD == Image(doc, S, t)
    <1> DEFINE pairs == DueN(imD, t)
    <1> DEFINE docL == ImgN(imD, pairs)
    <1> DEFINE mid == ImgN(imB, pairs)
    <1> DEFINE calls == DueC(docL, t)
    <1>1. S \subseteq DOMAIN doc /\ DOMAIN doc \subseteq DOMAIN base
        BY Zenon
    <1>2. S \subseteq DOMAIN base
        BY <1>1, Zenon
    <1>3. DOMAIN imD = DOMAIN doc /\ DOMAIN imB = DOMAIN base
        BY <1>1, <1>2, ImageDom DEF imD, imB
    <1>4. \A k \in DOMAIN imD : imD[k].promise.callbacks \subseteq Id
        BY <1>1, CallsOn DEF imD
    <1>5. \A k \in DOMAIN imD : P!Project(imD[k], t) = imD[k]
        BY <1>3, SliceFixed DEF imD
    <1>6. SweepCallbacks(docL, t).doc = ImgC(docL, calls, t)
        BY <1>4, <1>5, CallAfter DEF docL, pairs, imD, calls
    <1>7. imB = [ i \in DOMAIN imB |-> imB[i] ]
        BY <1>2, EtaImage DEF imB
    <1>8. mid = [ i \in DOMAIN mid |-> mid[i] ]
        BY <1>7, EtaImgN DEF mid, pairs, imB
    <1>9. DOMAIN docL = DOMAIN imD /\ DOMAIN mid = DOMAIN imB
        <2>1. CASE pairs = {}
            <3>1. docL = imD /\ mid = imB
                BY <2>1 DEF docL, mid, ImgN
            <3>2. QED
                BY <3>1
        <2>2. CASE pairs # {}
            <3> DEFINE bD == [ j \in DOMAIN imD |-> BodyN(imD, pairs, j) ]
            <3> DEFINE bB == [ j \in DOMAIN imB |-> BodyN(imB, pairs, j) ]
            <3>1. docL = bD /\ mid = bB
                BY <2>2 DEF docL, mid, ImgN, bD, bB
            <3>2. DOMAIN bD = DOMAIN imD /\ DOMAIN bB = DOMAIN imB
                BY DomCtor DEF bD, bB
            <3>3. QED
                BY <3>1, <3>2
        <2>3. QED
            BY <2>1, <2>2
    <1>10. DOMAIN docL = { i \in DOMAIN mid : i.origin = o }
        BY <1>3, <1>9, Zenon
    <1>11. ASSUME NEW k \in DOMAIN imD
           PROVE  imB[k] = imD[k]
        <2>1. k \in DOMAIN doc /\ k \in DOMAIN base
            BY <1>3, <1>11, Zenon
        <2>2. base[k] = doc[k]
            BY <2>1, Zenon
        <2>3. imD[k] = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
            BY <1>1, <2>1, ImageVal DEF imD
        <2>4. imB[k] = IF k \in S THEN P!Project(base[k], t) ELSE base[k]
            BY <1>2, <2>1, ImageVal DEF imB
        <2>5. P!Project(base[k], t) = P!Project(doc[k], t)
            BY <2>2, Zenon
        <2>6. QED
            BY <2>2, <2>3, <2>4, <2>5, Z3
    <1>12. \A k \in DOMAIN docL : mid[k] = docL[k]
        <2> SUFFICES ASSUME NEW k \in DOMAIN docL
                     PROVE  mid[k] = docL[k]
            OBVIOUS
        <2>1. k \in DOMAIN imD /\ k \in DOMAIN imB /\ imB[k] = imD[k]
            BY <1>1, <1>3, <1>9, <1>11, Zenon
        <2>2. CASE pairs = {}
            <3>1. docL = imD /\ mid = imB
                BY <2>2 DEF docL, mid, ImgN
            <3>2. QED
                BY <2>1, <3>1
        <2>3. CASE pairs # {}
            <3> DEFINE bD == [ j \in DOMAIN imD |-> BodyN(imD, pairs, j) ]
            <3> DEFINE bB == [ j \in DOMAIN imB |-> BodyN(imB, pairs, j) ]
            <3>1. docL = bD /\ mid = bB
                BY <2>3 DEF docL, mid, ImgN, bD, bB
            <3>2. bD[k] = BodyN(imD, pairs, k)
                BY <2>1, Zenon DEF bD
            <3>3. bB[k] = BodyN(imB, pairs, k)
                BY <2>1, Zenon DEF bB
            <3>4. BodyN(imB, pairs, k) = BodyN(imD, pairs, k)
                BY <2>1, SameBody
            <3>5. QED
                BY <3>1, <3>2, <3>3, <3>4
        <2>4. QED
            BY <2>2, <2>3
    <1>13. calls \subseteq [id : DOMAIN docL, awaiter : Id]
        BY AwSub DEF calls, docL
    <1>14. \A y \in calls :
              y.awaiter \in DOMAIN mid => y.awaiter \in DOMAIN docL
        <2>1. \A y \in [id : DOMAIN docL, awaiter : Id] :
                y.awaiter \in DOMAIN mid => y.awaiter \in DOMAIN docL
            <3> SUFFICES ASSUME NEW y \in [id : DOMAIN docL, awaiter : Id],
                                y.awaiter \in DOMAIN mid
                         PROVE  y.awaiter \in DOMAIN docL
                OBVIOUS
            <3>1. DOMAIN docL = DOMAIN doc /\ DOMAIN mid = DOMAIN base
                BY <1>3, <1>9, Zenon
            <3>2. y \in [id : DOMAIN doc, awaiter : Id]
                BY <3>1, Zenon
            <3>3. y.awaiter \in DOMAIN base
                BY <3>1, Zenon
            <3>4. y.awaiter \in DOMAIN doc
                BY <3>2, <3>3, Zenon
            <3>5. QED
                BY <3>1, <3>4, Zenon
        <2>2. QED
            BY <2>1, LocalDue DEF calls, docL, mid
    <1>15. Plant(mid, o, ImgC(docL, calls, t)) = ImgC(mid, calls, t)
        BY <1>8, <1>10, <1>12, <1>13, <1>14, PlantC DEF mid, docL, calls
    <1>16. QED
        BY <1>6, <1>15 DEF mid, docL, calls

(* An acquired task whose lease time is set, on a promise that is still
   pending, is exactly a due lease. Projection is already the identity, so
   the promise state is the real state. *)
LEMMA LeaseShape ==
    ASSUME NEW doc, NEW t,
           \A k \in DOMAIN doc : P!Project(doc[k], t) = doc[k],
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending"
    PROVE  { i \in DOMAIN doc :
               doc[i].task.state = "acquired"
               /\ doc[i].task.leaseTimeoutAt <= t }
           = DueL(doc, t)
PROOF
    <1> DEFINE exp ==
            { i \in DOMAIN doc :
                doc[i].task.state = "acquired"
                /\ doc[i].task.leaseTimeoutAt <= t }
    <1>1. exp \subseteq DueL(doc, t)
        <2> SUFFICES ASSUME NEW k \in exp
                     PROVE  k \in DueL(doc, t)
            OBVIOUS
        <2>1. /\ k \in DOMAIN doc
              /\ doc[k].task.state = "acquired"
              /\ doc[k].task.leaseTimeoutAt <= t
            BY DEF exp
        <2>2. doc[k].task.leaseTimeoutAt /= NoTime
              /\ doc[k].promise.state = "pending"
            BY <2>1, Zenon
        <2>3. P!Project(doc[k], t) = doc[k]
            BY <2>1
        <2>4. P!Project(doc[k], t).promise.state = doc[k].promise.state
            BY <2>3, Zenon
        <2>5. QED
            BY <2>1, <2>2, <2>4, Zenon DEF DueL
    <1>2. DueL(doc, t) \subseteq exp
        <2> SUFFICES ASSUME NEW k \in DueL(doc, t)
                     PROVE  k \in exp
            OBVIOUS
        <2>1. /\ k \in DOMAIN doc
              /\ doc[k].task.state = "acquired"
              /\ doc[k].task.leaseTimeoutAt <= t
            BY DEF DueL
        <2>2. QED
            BY <2>1 DEF exp
    <1>3. QED
        BY <1>1, <1>2, SetExtensionality DEF exp

LEMMA LeasesSub ==
    ASSUME NEW base, NEW doc, NEW t,
           DOMAIN doc \subseteq DOMAIN base,
           \A k \in DOMAIN doc : base[k] = doc[k]
    PROVE  DueL(doc, t) \subseteq DueL(base, t)
PROOF
    <1>1. ASSUME NEW k \in DueL(doc, t)
          PROVE  k \in DueL(base, t)
        <2>1. /\ k \in DOMAIN doc
              /\ doc[k].task.state = "acquired"
              /\ doc[k].task.leaseTimeoutAt /= NoTime
              /\ doc[k].task.leaseTimeoutAt <= t
              /\ P!Project(doc[k], t).promise.state = "pending"
            BY <1>1 DEF DueL
        <2>2. k \in DOMAIN base /\ base[k] = doc[k]
            BY <2>1, Zenon
        <2>3. P!Project(base[k], t) = P!Project(doc[k], t)
            BY <2>2, Zenon
        <2>4. QED
            BY <2>1, <2>2, <2>3, Zenon DEF DueL
    <1>2. QED
        BY <1>1

(* Due leases of one document are a chain in the whole store. The outbox
   stays. The document carries the lease shape. *)
LEMMA LeaseFrom ==
    ASSUME NEW base, NEW doc, NEW t, NEW box,
           DOMAIN doc \subseteq DOMAIN base,
           DOMAIN doc \subseteq Id,
           \A k \in DOMAIN doc : base[k] = doc[k],
           \A k \in DOMAIN doc : P!Project(doc[k], t) = doc[k],
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending"
    PROVE  ReachN(base, box, t,
                  ImgL(base,
                       { i \in DOMAIN doc :
                           doc[i].task.state = "acquired"
                           /\ doc[i].task.leaseTimeoutAt <= t },
                       t),
                  box,
                  Cardinality({ i \in DOMAIN doc :
                                  doc[i].task.state = "acquired"
                                  /\ doc[i].task.leaseTimeoutAt <= t }))
PROOF
    <1> DEFINE exp ==
            { i \in DOMAIN doc :
                doc[i].task.state = "acquired"
                /\ doc[i].task.leaseTimeoutAt <= t }
    <1>1. exp = DueL(doc, t)
        BY LeaseShape DEF exp
    <1>2. exp \subseteq DueL(base, t)
        BY <1>1, LeasesSub DEF exp
    <1>3. exp \subseteq Id
        <2>1. exp \subseteq DOMAIN doc
            BY <1>1, LeaseSubset DEF exp
        <2>2. QED
            BY <2>1, Zenon
    <1>4. IsFiniteSet(exp)
        BY <1>3, SubCap DEF exp
    <1>5. QED
        BY <1>2, <1>4, LeaseSub DEF exp

(* A pending task whose retry time is set, on a promise that is still
   pending, is exactly a due retry. *)
LEMMA RetryShape ==
    ASSUME NEW doc, NEW t,
           \A k \in DOMAIN doc : P!Project(doc[k], t) = doc[k],
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending"
    PROVE  { i \in DOMAIN doc :
               doc[i].task.state = "pending"
               /\ doc[i].task.retryTimeoutAt <= t }
           = DueR(doc, t)
PROOF
    <1> DEFINE exp ==
            { i \in DOMAIN doc :
                doc[i].task.state = "pending"
                /\ doc[i].task.retryTimeoutAt <= t }
    <1>1. exp \subseteq DueR(doc, t)
        <2> SUFFICES ASSUME NEW k \in exp
                     PROVE  k \in DueR(doc, t)
            OBVIOUS
        <2>1. /\ k \in DOMAIN doc
              /\ doc[k].task.state = "pending"
              /\ doc[k].task.retryTimeoutAt <= t
            BY DEF exp
        <2>2. doc[k].task.retryTimeoutAt /= NoTime
              /\ doc[k].promise.state = "pending"
            BY <2>1, Zenon
        <2>3. P!Project(doc[k], t) = doc[k]
            BY <2>1
        <2>4. P!Project(doc[k], t).promise.state = doc[k].promise.state
            BY <2>3, Zenon
        <2>5. QED
            BY <2>1, <2>2, <2>4, Zenon DEF DueR
    <1>2. DueR(doc, t) \subseteq exp
        <2> SUFFICES ASSUME NEW k \in DueR(doc, t)
                     PROVE  k \in exp
            OBVIOUS
        <2>1. /\ k \in DOMAIN doc
              /\ doc[k].task.state = "pending"
              /\ doc[k].task.retryTimeoutAt <= t
            BY DEF DueR
        <2>2. QED
            BY <2>1 DEF exp
    <1>3. QED
        BY <1>1, <1>2, SetExtensionality DEF exp

LEMMA RetriesSub ==
    ASSUME NEW base, NEW doc, NEW t,
           DOMAIN doc \subseteq DOMAIN base,
           \A k \in DOMAIN doc : base[k] = doc[k]
    PROVE  DueR(doc, t) \subseteq DueR(base, t)
PROOF
    <1>1. ASSUME NEW k \in DueR(doc, t)
          PROVE  k \in DueR(base, t)
        <2>1. /\ k \in DOMAIN doc
              /\ doc[k].task.state = "pending"
              /\ doc[k].task.retryTimeoutAt /= NoTime
              /\ doc[k].task.retryTimeoutAt <= t
              /\ P!Project(doc[k], t).promise.state = "pending"
            BY <1>1 DEF DueR
        <2>2. k \in DOMAIN base /\ base[k] = doc[k]
            BY <2>1, Zenon
        <2>3. P!Project(base[k], t) = P!Project(doc[k], t)
            BY <2>2, Zenon
        <2>4. QED
            BY <2>1, <2>2, <2>3, Zenon DEF DueR
    <1>2. QED
        BY <1>1

(* Due retries of one document are a chain in the whole store. Each posts
   its Execute. The document carries the retry shape. *)
LEMMA RetryFrom ==
    ASSUME NEW base, NEW doc, NEW t, NEW box,
           DOMAIN doc \subseteq DOMAIN base,
           DOMAIN doc \subseteq Id,
           \A k \in DOMAIN doc : base[k] = doc[k],
           \A k \in DOMAIN doc : P!Project(doc[k], t) = doc[k],
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending"
    PROVE  ReachN(base, box, t,
                  ImgR(base,
                       { i \in DOMAIN doc :
                           doc[i].task.state = "pending"
                           /\ doc[i].task.retryTimeoutAt <= t },
                       t),
                  BoxAt(box, base,
                        { i \in DOMAIN doc :
                            doc[i].task.state = "pending"
                            /\ doc[i].task.retryTimeoutAt <= t }),
                  Cardinality({ i \in DOMAIN doc :
                                  doc[i].task.state = "pending"
                                  /\ doc[i].task.retryTimeoutAt <= t }))
PROOF
    <1> DEFINE exp ==
            { i \in DOMAIN doc :
                doc[i].task.state = "pending"
                /\ doc[i].task.retryTimeoutAt <= t }
    <1>1. exp = DueR(doc, t)
        BY RetryShape DEF exp
    <1>2. exp \subseteq DueR(base, t)
        BY <1>1, RetriesSub DEF exp
    <1>3. exp \subseteq Id
        <2>1. exp \subseteq DOMAIN doc
            BY <1>1, RetrySubset DEF exp
        <2>2. QED
            BY <2>1, Zenon
    <1>4. IsFiniteSet(exp)
        BY <1>3, SubCap DEF exp
    <1>5. QED
        BY <1>2, <1>4, RetrySub DEF exp

===============================================================================
