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

(* Projecting a due promise fulfills its task, so an acquired or pending
   task that remains still has the lease or retry time the due sets ask for. *)
LEMMA ShapeObj ==
    ASSUME NEW obj, NEW t,
           obj.task.state = "acquired" =>
               /\ obj.task.leaseTimeoutAt /= NoTime
               /\ obj.promise.state = "pending",
           obj.task.state = "pending" =>
               /\ obj.task.retryTimeoutAt /= NoTime
               /\ obj.promise.state = "pending"
    PROVE  /\ P!Project(obj, t).task.state = "acquired" =>
                 /\ P!Project(obj, t).task.leaseTimeoutAt /= NoTime
                 /\ P!Project(obj, t).promise.state = "pending"
           /\ P!Project(obj, t).task.state = "pending" =>
                 /\ P!Project(obj, t).task.retryTimeoutAt /= NoTime
                 /\ P!Project(obj, t).promise.state = "pending"
PROOF
    <1>1. CASE obj.promise.state = "pending" /\ obj.promise.timeoutAt <= t
        <2> DEFINE p == P!Project(obj, t)
        <2> DEFINE ts == IF obj.task.state = "none" THEN "none" ELSE "fulfilled"
        <2> DEFINE task1 ==
                [obj.task EXCEPT !.state          = ts,
                                 !.pid            = NoPid,
                                 !.ttl            = P!NoTime,
                                 !.leaseTimeoutAt = P!NoTime,
                                 !.retryTimeoutAt = P!NoTime,
                                 !.resumes        = {}]
        <2>1. p.task = task1
            BY <1>1, Z3 DEF p, ts, task1, P!Project
        <2>2. task1.state = ts
            BY Z3 DEF task1
        <2>3. ts = "none" \/ ts = "fulfilled"
            BY Z3 DEF ts
        <2>4. p.task.state /= "acquired" /\ p.task.state /= "pending"
            BY <2>1, <2>2, <2>3, Zenon
        <2>5. QED
            BY <2>4, Zenon DEF p
    <1>2. CASE obj.promise.state /= "pending" \/ ~(obj.promise.timeoutAt <= t)
        <2>1. P!Project(obj, t) = obj
            BY <1>2, ProjectId
        <2>2. QED
            BY <2>1, Zenon
    <1>3. QED
        BY <1>1, <1>2

LEMMA LeaseOn ==
    ASSUME NEW doc, NEW t, NEW S,
           S \subseteq DOMAIN doc,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending"
    PROVE  \A k \in DOMAIN Image(doc, S, t) :
               Image(doc, S, t)[k].task.state = "acquired" =>
                   /\ Image(doc, S, t)[k].task.leaseTimeoutAt /= NoTime
                   /\ Image(doc, S, t)[k].promise.state = "pending"
PROOF
    <1>1. DOMAIN Image(doc, S, t) = DOMAIN doc
        BY ImageDom
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  Image(doc, S, t)[k].task.state = "acquired" =>
                     /\ Image(doc, S, t)[k].task.leaseTimeoutAt /= NoTime
                     /\ Image(doc, S, t)[k].promise.state = "pending"
        <2>1. /\ k \in DOMAIN Image(doc, S, t)
              /\ Image(doc, S, t)[k]
                    = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
            BY <1>2, ImageVal
        <2>2. CASE k \in S
            <3>1. Image(doc, S, t)[k] = P!Project(doc[k], t)
                BY <2>1, <2>2
            <3>2. doc[k].task.state = "acquired" =>
                      /\ doc[k].task.leaseTimeoutAt /= NoTime
                      /\ doc[k].promise.state = "pending"
                BY <1>2, Zenon
            <3>3. doc[k].task.state = "pending" =>
                      /\ doc[k].task.retryTimeoutAt /= NoTime
                      /\ doc[k].promise.state = "pending"
                BY <1>2, Zenon
            <3>4. P!Project(doc[k], t).task.state = "acquired" =>
                      /\ P!Project(doc[k], t).task.leaseTimeoutAt /= NoTime
                      /\ P!Project(doc[k], t).promise.state = "pending"
                BY <3>2, <3>3, ShapeObj
            <3>5. QED
                BY <3>1, <3>4, Zenon
        <2>3. CASE k \notin S
            <3>1. Image(doc, S, t)[k] = doc[k]
                BY <2>1, <2>3
            <3>2. QED
                BY <1>2, <3>1, Zenon
        <2>4. QED
            BY <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2, Z3

LEMMA RetryOn ==
    ASSUME NEW doc, NEW t, NEW S,
           S \subseteq DOMAIN doc,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending"
    PROVE  \A k \in DOMAIN Image(doc, S, t) :
               Image(doc, S, t)[k].task.state = "pending" =>
                   /\ Image(doc, S, t)[k].task.retryTimeoutAt /= NoTime
                   /\ Image(doc, S, t)[k].promise.state = "pending"
PROOF
    <1>1. DOMAIN Image(doc, S, t) = DOMAIN doc
        BY ImageDom
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  Image(doc, S, t)[k].task.state = "pending" =>
                     /\ Image(doc, S, t)[k].task.retryTimeoutAt /= NoTime
                     /\ Image(doc, S, t)[k].promise.state = "pending"
        <2>1. /\ k \in DOMAIN Image(doc, S, t)
              /\ Image(doc, S, t)[k]
                    = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
            BY <1>2, ImageVal
        <2>2. CASE k \in S
            <3>1. Image(doc, S, t)[k] = P!Project(doc[k], t)
                BY <2>1, <2>2
            <3>2. doc[k].task.state = "acquired" =>
                      /\ doc[k].task.leaseTimeoutAt /= NoTime
                      /\ doc[k].promise.state = "pending"
                BY <1>2, Zenon
            <3>3. doc[k].task.state = "pending" =>
                      /\ doc[k].task.retryTimeoutAt /= NoTime
                      /\ doc[k].promise.state = "pending"
                BY <1>2, Zenon
            <3>4. P!Project(doc[k], t).task.state = "pending" =>
                      /\ P!Project(doc[k], t).task.retryTimeoutAt /= NoTime
                      /\ P!Project(doc[k], t).promise.state = "pending"
                BY <3>2, <3>3, ShapeObj
            <3>5. QED
                BY <3>1, <3>4, Zenon
        <2>3. CASE k \notin S
            <3>1. Image(doc, S, t)[k] = doc[k]
                BY <2>1, <2>3
            <3>2. QED
                BY <1>2, <3>1, Zenon
        <2>4. QED
            BY <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2, Z3

LEMMA LeaseCopy ==
    ASSUME NEW out, NEW src,
           out.task.state = src.task.state,
           out.task.leaseTimeoutAt = src.task.leaseTimeoutAt,
           out.promise.state = src.promise.state,
           src.task.state = "acquired" =>
               /\ src.task.leaseTimeoutAt /= NoTime
               /\ src.promise.state = "pending"
    PROVE  out.task.state = "acquired" =>
               /\ out.task.leaseTimeoutAt /= NoTime
               /\ out.promise.state = "pending"
PROOF
    BY Zenon

LEMMA RetryCopy ==
    ASSUME NEW out, NEW src,
           out.task.state = src.task.state,
           out.task.retryTimeoutAt = src.task.retryTimeoutAt,
           out.promise.state = src.promise.state,
           src.task.state = "pending" =>
               /\ src.task.retryTimeoutAt /= NoTime
               /\ src.promise.state = "pending"
    PROVE  out.task.state = "pending" =>
               /\ out.task.retryTimeoutAt /= NoTime
               /\ out.promise.state = "pending"
PROOF
    BY Zenon

LEMMA SuspendCopy ==
    ASSUME NEW out, NEW src,
           out.task.state = src.task.state,
           out.promise.state = src.promise.state,
           src.task.state = "suspended" => src.promise.state = "pending"
    PROVE  out.task.state = "suspended" => out.promise.state = "pending"
PROOF
    BY Zenon

(* Dropping listeners copies the task and the promise state. *)
LEMMA ShapeStruck ==
    ASSUME NEW obj, NEW G,
           obj.task.state = "acquired" =>
               /\ obj.task.leaseTimeoutAt /= NoTime
               /\ obj.promise.state = "pending",
           obj.task.state = "pending" =>
               /\ obj.task.retryTimeoutAt /= NoTime
               /\ obj.promise.state = "pending",
           obj.task.state = "suspended" => obj.promise.state = "pending"
    PROVE  /\ Struck(obj, G).task.state = "acquired" =>
                 /\ Struck(obj, G).task.leaseTimeoutAt /= NoTime
                 /\ Struck(obj, G).promise.state = "pending"
           /\ Struck(obj, G).task.state = "pending" =>
                 /\ Struck(obj, G).task.retryTimeoutAt /= NoTime
                 /\ Struck(obj, G).promise.state = "pending"
           /\ Struck(obj, G).task.state = "suspended" =>
                 Struck(obj, G).promise.state = "pending"
PROOF
    <1> DEFINE s == Struck(obj, G)
    <1>1. /\ s.task = obj.task
          /\ s.promise.state = obj.promise.state
        BY Z3 DEF s, Struck
    <1>2. s.task.state = obj.task.state
        BY <1>1, Z3
    <1>3. s.task.leaseTimeoutAt = obj.task.leaseTimeoutAt
        BY <1>1, Z3
    <1>4. s.task.retryTimeoutAt = obj.task.retryTimeoutAt
        BY <1>1, Z3
    <1>5. s.task.state = "acquired" =>
              /\ s.task.leaseTimeoutAt /= NoTime
              /\ s.promise.state = "pending"
        BY <1>1, <1>2, <1>3, LeaseCopy DEF s
    <1>6. s.task.state = "pending" =>
              /\ s.task.retryTimeoutAt /= NoTime
              /\ s.promise.state = "pending"
        BY <1>1, <1>2, <1>4, RetryCopy DEF s
    <1>7. s.task.state = "suspended" => s.promise.state = "pending"
        BY <1>1, <1>2, SuspendCopy DEF s
    <1>8. QED
        BY <1>5, <1>6, <1>7 DEF s

LEMMA DomImgN ==
    ASSUME NEW doc, NEW Q
    PROVE  DOMAIN ImgN(doc, Q) = DOMAIN doc
PROOF
    <1>1. CASE Q = {}
        BY <1>1 DEF ImgN
    <1>2. CASE Q # {}
        <2> DEFINE im == [ j \in DOMAIN doc |-> BodyN(doc, Q, j) ]
        <2>1. ImgN(doc, Q) = im
            BY <1>2 DEF ImgN, im
        <2>2. DOMAIN im = DOMAIN doc
            BY DomCtor DEF im
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2

LEMMA ShapeBodyN ==
    ASSUME NEW doc, NEW Q, NEW k,
           k \in DOMAIN doc,
           doc[k].task.state = "acquired" =>
               /\ doc[k].task.leaseTimeoutAt /= NoTime
               /\ doc[k].promise.state = "pending",
           doc[k].task.state = "pending" =>
               /\ doc[k].task.retryTimeoutAt /= NoTime
               /\ doc[k].promise.state = "pending",
           doc[k].task.state = "suspended" =>
               doc[k].promise.state = "pending"
    PROVE  /\ ImgN(doc, Q)[k].task.state = "acquired" =>
                 /\ ImgN(doc, Q)[k].task.leaseTimeoutAt /= NoTime
                 /\ ImgN(doc, Q)[k].promise.state = "pending"
           /\ ImgN(doc, Q)[k].task.state = "pending" =>
                 /\ ImgN(doc, Q)[k].task.retryTimeoutAt /= NoTime
                 /\ ImgN(doc, Q)[k].promise.state = "pending"
           /\ ImgN(doc, Q)[k].task.state = "suspended" =>
                 ImgN(doc, Q)[k].promise.state = "pending"
PROOF
    <1>1. CASE Q = {}
        <2>1. ImgN(doc, Q) = doc
            BY <1>1 DEF ImgN
        <2>2. ImgN(doc, Q)[k] = doc[k]
            BY <2>1, Zenon
        <2>3. QED
            BY <2>2, Zenon
    <1>2. CASE Q # {}
        <2> DEFINE im == [ j \in DOMAIN doc |-> BodyN(doc, Q, j) ]
        <2>1. ImgN(doc, Q) = im
            BY <1>2 DEF ImgN, im
        <2>2. DOMAIN im = DOMAIN doc
            BY DomCtor DEF im
        <2>3. im[k] = BodyN(doc, Q, k)
            BY <2>2, Zenon DEF im
        <2>4. CASE Gone(k, Q) = {}
            <3>1. BodyN(doc, Q, k)
                    = (LET g == Gone(k, Q)
                       IN  IF g = {} THEN doc[k] ELSE Struck(doc[k], g))
                BY BodyWhen
            <3>2. BodyN(doc, Q, k) = doc[k]
                BY ONLY <2>4, <3>1, Zenon
            <3>3. im[k] = doc[k]
                BY <2>3, <3>2
            <3>4. QED
                BY <2>1, <3>3, Zenon
        <2>5. CASE Gone(k, Q) # {}
            <3> DEFINE s == Struck(doc[k], Gone(k, Q))
            <3>1. BodyN(doc, Q, k)
                    = (LET g == Gone(k, Q)
                       IN  IF g = {} THEN doc[k] ELSE Struck(doc[k], g))
                BY BodyWhen
            <3>2. BodyN(doc, Q, k) = s
                BY ONLY <2>5, <3>1, Zenon DEF s
            <3>3. /\ s.task.state = "acquired" =>
                        /\ s.task.leaseTimeoutAt /= NoTime
                        /\ s.promise.state = "pending"
                  /\ s.task.state = "pending" =>
                        /\ s.task.retryTimeoutAt /= NoTime
                        /\ s.promise.state = "pending"
                  /\ s.task.state = "suspended" =>
                        s.promise.state = "pending"
                BY ShapeStruck DEF s
            <3>4. im[k] = s
                BY <2>3, <3>2
            <3>5. QED
                BY <2>1, <3>3, <3>4, Zenon
        <2>6. QED
            BY <2>4, <2>5
    <1>3. QED
        BY <1>1, <1>2

LEMMA LeaseN ==
    ASSUME NEW doc, NEW Q,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  \A k \in DOMAIN ImgN(doc, Q) :
               ImgN(doc, Q)[k].task.state = "acquired" =>
                   /\ ImgN(doc, Q)[k].task.leaseTimeoutAt /= NoTime
                   /\ ImgN(doc, Q)[k].promise.state = "pending"
PROOF
    <1>1. DOMAIN ImgN(doc, Q) = DOMAIN doc
        BY DomImgN
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  ImgN(doc, Q)[k].task.state = "acquired" =>
                     /\ ImgN(doc, Q)[k].task.leaseTimeoutAt /= NoTime
                     /\ ImgN(doc, Q)[k].promise.state = "pending"
        <2>1. doc[k].task.state = "acquired" =>
                  /\ doc[k].task.leaseTimeoutAt /= NoTime
                  /\ doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>2. doc[k].task.state = "pending" =>
                  /\ doc[k].task.retryTimeoutAt /= NoTime
                  /\ doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>3. doc[k].task.state = "suspended" =>
                  doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>4. /\ ImgN(doc, Q)[k].task.state = "acquired" =>
                    /\ ImgN(doc, Q)[k].task.leaseTimeoutAt /= NoTime
                    /\ ImgN(doc, Q)[k].promise.state = "pending"
              /\ ImgN(doc, Q)[k].task.state = "pending" =>
                    /\ ImgN(doc, Q)[k].task.retryTimeoutAt /= NoTime
                    /\ ImgN(doc, Q)[k].promise.state = "pending"
              /\ ImgN(doc, Q)[k].task.state = "suspended" =>
                    ImgN(doc, Q)[k].promise.state = "pending"
            BY <1>2, <2>1, <2>2, <2>3, ShapeBodyN
        <2>5. QED
            BY <2>4, Zenon
    <1>3. QED
        BY <1>1, <1>2, Z3

LEMMA RetryN ==
    ASSUME NEW doc, NEW Q,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  \A k \in DOMAIN ImgN(doc, Q) :
               ImgN(doc, Q)[k].task.state = "pending" =>
                   /\ ImgN(doc, Q)[k].task.retryTimeoutAt /= NoTime
                   /\ ImgN(doc, Q)[k].promise.state = "pending"
PROOF
    <1>1. DOMAIN ImgN(doc, Q) = DOMAIN doc
        BY DomImgN
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  ImgN(doc, Q)[k].task.state = "pending" =>
                     /\ ImgN(doc, Q)[k].task.retryTimeoutAt /= NoTime
                     /\ ImgN(doc, Q)[k].promise.state = "pending"
        <2>1. doc[k].task.state = "acquired" =>
                  /\ doc[k].task.leaseTimeoutAt /= NoTime
                  /\ doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>2. doc[k].task.state = "pending" =>
                  /\ doc[k].task.retryTimeoutAt /= NoTime
                  /\ doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>3. doc[k].task.state = "suspended" =>
                  doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>4. /\ ImgN(doc, Q)[k].task.state = "acquired" =>
                    /\ ImgN(doc, Q)[k].task.leaseTimeoutAt /= NoTime
                    /\ ImgN(doc, Q)[k].promise.state = "pending"
              /\ ImgN(doc, Q)[k].task.state = "pending" =>
                    /\ ImgN(doc, Q)[k].task.retryTimeoutAt /= NoTime
                    /\ ImgN(doc, Q)[k].promise.state = "pending"
              /\ ImgN(doc, Q)[k].task.state = "suspended" =>
                    ImgN(doc, Q)[k].promise.state = "pending"
            BY <1>2, <2>1, <2>2, <2>3, ShapeBodyN
        <2>5. QED
            BY <2>4, Zenon
    <1>3. QED
        BY <1>1, <1>2, Z3

LEMMA SuspendN ==
    ASSUME NEW doc, NEW Q,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  \A k \in DOMAIN ImgN(doc, Q) :
               ImgN(doc, Q)[k].task.state = "suspended" =>
                   ImgN(doc, Q)[k].promise.state = "pending"
PROOF
    <1>1. DOMAIN ImgN(doc, Q) = DOMAIN doc
        BY DomImgN
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  ImgN(doc, Q)[k].task.state = "suspended" =>
                     ImgN(doc, Q)[k].promise.state = "pending"
        <2>1. doc[k].task.state = "acquired" =>
                  /\ doc[k].task.leaseTimeoutAt /= NoTime
                  /\ doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>2. doc[k].task.state = "pending" =>
                  /\ doc[k].task.retryTimeoutAt /= NoTime
                  /\ doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>3. doc[k].task.state = "suspended" =>
                  doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>4. /\ ImgN(doc, Q)[k].task.state = "acquired" =>
                    /\ ImgN(doc, Q)[k].task.leaseTimeoutAt /= NoTime
                    /\ ImgN(doc, Q)[k].promise.state = "pending"
              /\ ImgN(doc, Q)[k].task.state = "pending" =>
                    /\ ImgN(doc, Q)[k].task.retryTimeoutAt /= NoTime
                    /\ ImgN(doc, Q)[k].promise.state = "pending"
              /\ ImgN(doc, Q)[k].task.state = "suspended" =>
                    ImgN(doc, Q)[k].promise.state = "pending"
            BY <1>2, <2>1, <2>2, <2>3, ShapeBodyN
        <2>5. QED
            BY <2>4, Zenon
    <1>3. QED
        BY <1>1, <1>2, Z3

(* Dropping callbacks copies the task and the promise state. *)
LEMMA ShapeClear ==
    ASSUME NEW obj, NEW G,
           obj.task.state = "acquired" =>
               /\ obj.task.leaseTimeoutAt /= NoTime
               /\ obj.promise.state = "pending",
           obj.task.state = "pending" =>
               /\ obj.task.retryTimeoutAt /= NoTime
               /\ obj.promise.state = "pending",
           obj.task.state = "suspended" => obj.promise.state = "pending"
    PROVE  /\ P!WithoutCallbacks(obj, G).task.state = "acquired" =>
                 /\ P!WithoutCallbacks(obj, G).task.leaseTimeoutAt /= NoTime
                 /\ P!WithoutCallbacks(obj, G).promise.state = "pending"
           /\ P!WithoutCallbacks(obj, G).task.state = "pending" =>
                 /\ P!WithoutCallbacks(obj, G).task.retryTimeoutAt /= NoTime
                 /\ P!WithoutCallbacks(obj, G).promise.state = "pending"
           /\ P!WithoutCallbacks(obj, G).task.state = "suspended" =>
                 P!WithoutCallbacks(obj, G).promise.state = "pending"
PROOF
    <1> DEFINE c == P!WithoutCallbacks(obj, G)
    <1>1. /\ c.task = obj.task
          /\ c.promise.state = obj.promise.state
        BY Z3 DEF c, P!WithoutCallbacks
    <1>2. c.task.state = obj.task.state
        BY <1>1, Z3
    <1>3. c.task.leaseTimeoutAt = obj.task.leaseTimeoutAt
        BY <1>1, Z3
    <1>4. c.task.retryTimeoutAt = obj.task.retryTimeoutAt
        BY <1>1, Z3
    <1>5. c.task.state = "acquired" =>
              /\ c.task.leaseTimeoutAt /= NoTime
              /\ c.promise.state = "pending"
        BY <1>1, <1>2, <1>3, LeaseCopy DEF c
    <1>6. c.task.state = "pending" =>
              /\ c.task.retryTimeoutAt /= NoTime
              /\ c.promise.state = "pending"
        BY <1>1, <1>2, <1>4, RetryCopy DEF c
    <1>7. c.task.state = "suspended" => c.promise.state = "pending"
        BY <1>1, <1>2, SuspendCopy DEF c
    <1>8. QED
        BY <1>5, <1>6, <1>7 DEF c

LEMMA ShapeCleared ==
    ASSUME NEW doc, NEW S, NEW j,
           doc[j].task.state = "acquired" =>
               /\ doc[j].task.leaseTimeoutAt /= NoTime
               /\ doc[j].promise.state = "pending",
           doc[j].task.state = "pending" =>
               /\ doc[j].task.retryTimeoutAt /= NoTime
               /\ doc[j].promise.state = "pending",
           doc[j].task.state = "suspended" =>
               doc[j].promise.state = "pending"
    PROVE  /\ Cleared(doc, S, j).task.state = "acquired" =>
                 /\ Cleared(doc, S, j).task.leaseTimeoutAt /= NoTime
                 /\ Cleared(doc, S, j).promise.state = "pending"
           /\ Cleared(doc, S, j).task.state = "pending" =>
                 /\ Cleared(doc, S, j).task.retryTimeoutAt /= NoTime
                 /\ Cleared(doc, S, j).promise.state = "pending"
           /\ Cleared(doc, S, j).task.state = "suspended" =>
                 Cleared(doc, S, j).promise.state = "pending"
PROOF
    <1> DEFINE g == Drp(j, S)
    <1> DEFINE c == Cleared(doc, S, j)
    <1>1. c = (IF g = {} THEN doc[j] ELSE P!WithoutCallbacks(doc[j], g))
        BY DEF c, Cleared, g
    <1>2. CASE g = {}
        <2>1. c = doc[j]
            BY <1>1, <1>2, Z3 DEF c
        <2>2. QED
            BY <2>1, Zenon DEF c
    <1>3. CASE g # {}
        <2> DEFINE u == P!WithoutCallbacks(doc[j], g)
        <2>1. c = u
            BY <1>1, <1>3, Z3 DEF c, u
        <2>2. /\ u.task.state = "acquired" =>
                    /\ u.task.leaseTimeoutAt /= NoTime
                    /\ u.promise.state = "pending"
              /\ u.task.state = "pending" =>
                    /\ u.task.retryTimeoutAt /= NoTime
                    /\ u.promise.state = "pending"
              /\ u.task.state = "suspended" =>
                    u.promise.state = "pending"
            BY ShapeClear DEF u
        <2>3. QED
            BY <2>1, <2>2, Zenon DEF c
    <1>4. QED
        BY <1>2, <1>3

(* Waking a suspended task makes it pending at this time. Every other
   branch copies the task state and the promise state. *)
LEMMA ShapeWake ==
    ASSUME NEW obj, NEW srcs, NEW t,
           t /= NoTime,
           obj.task.state = "acquired" =>
               /\ obj.task.leaseTimeoutAt /= NoTime
               /\ obj.promise.state = "pending",
           obj.task.state = "pending" =>
               /\ obj.task.retryTimeoutAt /= NoTime
               /\ obj.promise.state = "pending",
           obj.task.state = "suspended" => obj.promise.state = "pending"
    PROVE  /\ Woken(obj, srcs, t).task.state = "acquired" =>
                 /\ Woken(obj, srcs, t).task.leaseTimeoutAt /= NoTime
                 /\ Woken(obj, srcs, t).promise.state = "pending"
           /\ Woken(obj, srcs, t).task.state = "pending" =>
                 /\ Woken(obj, srcs, t).task.retryTimeoutAt /= NoTime
                 /\ Woken(obj, srcs, t).promise.state = "pending"
           /\ Woken(obj, srcs, t).task.state = "suspended" =>
                 Woken(obj, srcs, t).promise.state = "pending"
PROOF
    <1> DEFINE w == Woken(obj, srcs, t)
    <1>1. CASE srcs = {}
        <2>1. w = obj
            BY <1>1, Z3 DEF w, Woken
        <2>2. /\ w.task.state = obj.task.state
              /\ w.task.leaseTimeoutAt = obj.task.leaseTimeoutAt
              /\ w.task.retryTimeoutAt = obj.task.retryTimeoutAt
              /\ w.promise.state = obj.promise.state
            BY <2>1, Z3
        <2>3. w.task.state = "acquired" =>
                  /\ w.task.leaseTimeoutAt /= NoTime
                  /\ w.promise.state = "pending"
            BY <2>2, LeaseCopy DEF w
        <2>4. w.task.state = "pending" =>
                  /\ w.task.retryTimeoutAt /= NoTime
                  /\ w.promise.state = "pending"
            BY <2>2, RetryCopy DEF w
        <2>5. w.task.state = "suspended" => w.promise.state = "pending"
            BY <2>2, SuspendCopy DEF w
        <2>6. QED
            BY <2>3, <2>4, <2>5 DEF w
    <1>2. CASE srcs # {} /\ obj.task.state \in {"none", "fulfilled"}
        <2>1. w = obj
            BY <1>2, Z3 DEF w, Woken
        <2>2. /\ w.task.state = obj.task.state
              /\ w.task.leaseTimeoutAt = obj.task.leaseTimeoutAt
              /\ w.task.retryTimeoutAt = obj.task.retryTimeoutAt
              /\ w.promise.state = obj.promise.state
            BY <2>1, Z3
        <2>3. w.task.state = "acquired" =>
                  /\ w.task.leaseTimeoutAt /= NoTime
                  /\ w.promise.state = "pending"
            BY <2>2, LeaseCopy DEF w
        <2>4. w.task.state = "pending" =>
                  /\ w.task.retryTimeoutAt /= NoTime
                  /\ w.promise.state = "pending"
            BY <2>2, RetryCopy DEF w
        <2>5. w.task.state = "suspended" => w.promise.state = "pending"
            BY <2>2, SuspendCopy DEF w
        <2>6. QED
            BY <2>3, <2>4, <2>5 DEF w
    <1>3. CASE srcs # {} /\ obj.task.state = "suspended"
        <2> DEFINE wk == P!WakeSuspended(obj, srcs, t)
        <2>1. w = wk
            BY <1>3, Z3 DEF w, Woken, wk
        <2>2. obj.promise.state = "pending"
            BY <1>3, Zenon
        <2>3. /\ wk.task.state = "pending"
              /\ wk.task.retryTimeoutAt = t
              /\ wk.promise = obj.promise
            BY Z3 DEF wk, P!WakeSuspended
        <2>4. wk.promise.state = "pending"
            BY <2>2, <2>3, Z3
        <2>5. wk.task.retryTimeoutAt /= NoTime
            BY <2>3, Zenon
        <2>6. wk.task.state /= "acquired" /\ wk.task.state /= "suspended"
            BY <2>3, Zenon
        <2>7. wk.task.state = "acquired" =>
                  /\ wk.task.leaseTimeoutAt /= NoTime
                  /\ wk.promise.state = "pending"
            BY <2>6, Zenon
        <2>8. wk.task.state = "pending" =>
                  /\ wk.task.retryTimeoutAt /= NoTime
                  /\ wk.promise.state = "pending"
            BY <2>3, <2>4, <2>5, Zenon
        <2>9. wk.task.state = "suspended" => wk.promise.state = "pending"
            BY <2>6, Zenon
        <2>10. QED
            BY <2>1, <2>7, <2>8, <2>9, Zenon DEF w, wk
    <1>4. CASE srcs # {} /\ obj.task.state \notin {"none", "fulfilled"}
                       /\ obj.task.state /= "suspended"
        <2> DEFINE un == P!UnionResumes(obj, srcs)
        <2>1. w = un
            BY <1>4, Z3 DEF w, Woken, un
        <2>2. /\ un.task.state = obj.task.state
              /\ un.task.leaseTimeoutAt = obj.task.leaseTimeoutAt
              /\ un.task.retryTimeoutAt = obj.task.retryTimeoutAt
              /\ un.promise.state = obj.promise.state
            BY Z3 DEF un, P!UnionResumes
        <2>3. un.task.state = "acquired" =>
                  /\ un.task.leaseTimeoutAt /= NoTime
                  /\ un.promise.state = "pending"
            BY <2>2, LeaseCopy DEF un
        <2>4. un.task.state = "pending" =>
                  /\ un.task.retryTimeoutAt /= NoTime
                  /\ un.promise.state = "pending"
            BY <2>2, RetryCopy DEF un
        <2>5. un.task.state = "suspended" => un.promise.state = "pending"
            BY <2>2, SuspendCopy DEF un
        <2>6. QED
            BY <2>1, <2>3, <2>4, <2>5, Zenon DEF w, un
    <1>5. QED
        BY <1>1, <1>2, <1>3, <1>4

LEMMA ShapeBodyC ==
    ASSUME NEW doc, NEW S, NEW j, NEW t,
           t /= NoTime,
           doc[j].task.state = "acquired" =>
               /\ doc[j].task.leaseTimeoutAt /= NoTime
               /\ doc[j].promise.state = "pending",
           doc[j].task.state = "pending" =>
               /\ doc[j].task.retryTimeoutAt /= NoTime
               /\ doc[j].promise.state = "pending",
           doc[j].task.state = "suspended" =>
               doc[j].promise.state = "pending"
    PROVE  /\ BodyC(doc, S, j, t).task.state = "acquired" =>
                 /\ BodyC(doc, S, j, t).task.leaseTimeoutAt /= NoTime
                 /\ BodyC(doc, S, j, t).promise.state = "pending"
           /\ BodyC(doc, S, j, t).task.state = "pending" =>
                 /\ BodyC(doc, S, j, t).task.retryTimeoutAt /= NoTime
                 /\ BodyC(doc, S, j, t).promise.state = "pending"
           /\ BodyC(doc, S, j, t).task.state = "suspended" =>
                 BodyC(doc, S, j, t).promise.state = "pending"
PROOF
    <1> DEFINE c == Cleared(doc, S, j)
    <1> DEFINE srcs == Src(j, S)
    <1> DEFINE b == BodyC(doc, S, j, t)
    <1>1. /\ c.task.state = "acquired" =>
                /\ c.task.leaseTimeoutAt /= NoTime
                /\ c.promise.state = "pending"
          /\ c.task.state = "pending" =>
                /\ c.task.retryTimeoutAt /= NoTime
                /\ c.promise.state = "pending"
          /\ c.task.state = "suspended" =>
                c.promise.state = "pending"
        BY ShapeCleared DEF c
    <1>2. c.task.state = "acquired" =>
              /\ c.task.leaseTimeoutAt /= NoTime
              /\ c.promise.state = "pending"
        BY <1>1, Zenon DEF c
    <1>3. c.task.state = "pending" =>
              /\ c.task.retryTimeoutAt /= NoTime
              /\ c.promise.state = "pending"
        BY <1>1, Zenon DEF c
    <1>4. c.task.state = "suspended" => c.promise.state = "pending"
        BY <1>1, Zenon DEF c
    <1>5. /\ Woken(c, srcs, t).task.state = "acquired" =>
                /\ Woken(c, srcs, t).task.leaseTimeoutAt /= NoTime
                /\ Woken(c, srcs, t).promise.state = "pending"
          /\ Woken(c, srcs, t).task.state = "pending" =>
                /\ Woken(c, srcs, t).task.retryTimeoutAt /= NoTime
                /\ Woken(c, srcs, t).promise.state = "pending"
          /\ Woken(c, srcs, t).task.state = "suspended" =>
                Woken(c, srcs, t).promise.state = "pending"
        BY <1>2, <1>3, <1>4, ShapeWake DEF c, srcs
    <1>6. b = Woken(c, srcs, t)
        BY DEF b, BodyC, c, srcs
    <1>7. QED
        BY <1>5, <1>6, Zenon DEF b

LEMMA DomImgC ==
    ASSUME NEW doc, NEW S, NEW t
    PROVE  DOMAIN ImgC(doc, S, t) = DOMAIN doc
PROOF
    <1>1. CASE S = {}
        BY <1>1 DEF ImgC
    <1>2. CASE S # {}
        <2> DEFINE im == [ j \in DOMAIN doc |-> BodyC(doc, S, j, t) ]
        <2>1. ImgC(doc, S, t) = im
            BY <1>2 DEF ImgC, im
        <2>2. DOMAIN im = DOMAIN doc
            BY DomCtor DEF im
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2

LEMMA LeaseC ==
    ASSUME NEW doc, NEW S, NEW t,
           t /= NoTime,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  \A k \in DOMAIN ImgC(doc, S, t) :
               ImgC(doc, S, t)[k].task.state = "acquired" =>
                   /\ ImgC(doc, S, t)[k].task.leaseTimeoutAt /= NoTime
                   /\ ImgC(doc, S, t)[k].promise.state = "pending"
PROOF
    <1>1. DOMAIN ImgC(doc, S, t) = DOMAIN doc
        BY DomImgC
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  ImgC(doc, S, t)[k].task.state = "acquired" =>
                     /\ ImgC(doc, S, t)[k].task.leaseTimeoutAt /= NoTime
                     /\ ImgC(doc, S, t)[k].promise.state = "pending"
        <2>1. doc[k].task.state = "acquired" =>
                  /\ doc[k].task.leaseTimeoutAt /= NoTime
                  /\ doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>2. doc[k].task.state = "pending" =>
                  /\ doc[k].task.retryTimeoutAt /= NoTime
                  /\ doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>3. doc[k].task.state = "suspended" =>
                  doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>4. /\ BodyC(doc, S, k, t).task.state = "acquired" =>
                    /\ BodyC(doc, S, k, t).task.leaseTimeoutAt /= NoTime
                    /\ BodyC(doc, S, k, t).promise.state = "pending"
              /\ BodyC(doc, S, k, t).task.state = "pending" =>
                    /\ BodyC(doc, S, k, t).task.retryTimeoutAt /= NoTime
                    /\ BodyC(doc, S, k, t).promise.state = "pending"
              /\ BodyC(doc, S, k, t).task.state = "suspended" =>
                    BodyC(doc, S, k, t).promise.state = "pending"
            BY <2>1, <2>2, <2>3, ShapeBodyC
        <2>5. CASE S = {}
            <3>1. ImgC(doc, S, t) = doc
                BY <2>5 DEF ImgC
            <3>2. ImgC(doc, S, t)[k] = doc[k]
                BY <1>2, <3>1, Zenon
            <3>3. QED
                BY <2>1, <3>2, Zenon
        <2>6. CASE S # {}
            <3> DEFINE im == [ j \in DOMAIN doc |-> BodyC(doc, S, j, t) ]
            <3>1. ImgC(doc, S, t) = im
                BY <2>6 DEF ImgC, im
            <3>2. DOMAIN im = DOMAIN doc
                BY DomCtor DEF im
            <3>3. im[k] = BodyC(doc, S, k, t)
                BY <1>2, <3>2, Zenon DEF im
            <3>4. QED
                BY <2>4, <3>1, <3>3, Zenon
        <2>7. QED
            BY <2>5, <2>6
    <1>3. QED
        BY <1>1, <1>2, Z3

LEMMA RetryC ==
    ASSUME NEW doc, NEW S, NEW t,
           t /= NoTime,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  \A k \in DOMAIN ImgC(doc, S, t) :
               ImgC(doc, S, t)[k].task.state = "pending" =>
                   /\ ImgC(doc, S, t)[k].task.retryTimeoutAt /= NoTime
                   /\ ImgC(doc, S, t)[k].promise.state = "pending"
PROOF
    <1>1. DOMAIN ImgC(doc, S, t) = DOMAIN doc
        BY DomImgC
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  ImgC(doc, S, t)[k].task.state = "pending" =>
                     /\ ImgC(doc, S, t)[k].task.retryTimeoutAt /= NoTime
                     /\ ImgC(doc, S, t)[k].promise.state = "pending"
        <2>1. doc[k].task.state = "acquired" =>
                  /\ doc[k].task.leaseTimeoutAt /= NoTime
                  /\ doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>2. doc[k].task.state = "pending" =>
                  /\ doc[k].task.retryTimeoutAt /= NoTime
                  /\ doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>3. doc[k].task.state = "suspended" =>
                  doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>4. /\ BodyC(doc, S, k, t).task.state = "acquired" =>
                    /\ BodyC(doc, S, k, t).task.leaseTimeoutAt /= NoTime
                    /\ BodyC(doc, S, k, t).promise.state = "pending"
              /\ BodyC(doc, S, k, t).task.state = "pending" =>
                    /\ BodyC(doc, S, k, t).task.retryTimeoutAt /= NoTime
                    /\ BodyC(doc, S, k, t).promise.state = "pending"
              /\ BodyC(doc, S, k, t).task.state = "suspended" =>
                    BodyC(doc, S, k, t).promise.state = "pending"
            BY <2>1, <2>2, <2>3, ShapeBodyC
        <2>5. CASE S = {}
            <3>1. ImgC(doc, S, t) = doc
                BY <2>5 DEF ImgC
            <3>2. ImgC(doc, S, t)[k] = doc[k]
                BY <1>2, <3>1, Zenon
            <3>3. QED
                BY <2>2, <3>2, Zenon
        <2>6. CASE S # {}
            <3> DEFINE im == [ j \in DOMAIN doc |-> BodyC(doc, S, j, t) ]
            <3>1. ImgC(doc, S, t) = im
                BY <2>6 DEF ImgC, im
            <3>2. DOMAIN im = DOMAIN doc
                BY DomCtor DEF im
            <3>3. im[k] = BodyC(doc, S, k, t)
                BY <1>2, <3>2, Zenon DEF im
            <3>4. QED
                BY <2>4, <3>1, <3>3, Zenon
        <2>7. QED
            BY <2>5, <2>6
    <1>3. QED
        BY <1>1, <1>2, Z3

LEMMA SuspendC ==
    ASSUME NEW doc, NEW S, NEW t,
           t /= NoTime,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  \A k \in DOMAIN ImgC(doc, S, t) :
               ImgC(doc, S, t)[k].task.state = "suspended" =>
                   ImgC(doc, S, t)[k].promise.state = "pending"
PROOF
    <1>1. DOMAIN ImgC(doc, S, t) = DOMAIN doc
        BY DomImgC
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  ImgC(doc, S, t)[k].task.state = "suspended" =>
                     ImgC(doc, S, t)[k].promise.state = "pending"
        <2>1. doc[k].task.state = "acquired" =>
                  /\ doc[k].task.leaseTimeoutAt /= NoTime
                  /\ doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>2. doc[k].task.state = "pending" =>
                  /\ doc[k].task.retryTimeoutAt /= NoTime
                  /\ doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>3. doc[k].task.state = "suspended" =>
                  doc[k].promise.state = "pending"
            BY <1>2, Zenon
        <2>4. /\ BodyC(doc, S, k, t).task.state = "acquired" =>
                    /\ BodyC(doc, S, k, t).task.leaseTimeoutAt /= NoTime
                    /\ BodyC(doc, S, k, t).promise.state = "pending"
              /\ BodyC(doc, S, k, t).task.state = "pending" =>
                    /\ BodyC(doc, S, k, t).task.retryTimeoutAt /= NoTime
                    /\ BodyC(doc, S, k, t).promise.state = "pending"
              /\ BodyC(doc, S, k, t).task.state = "suspended" =>
                    BodyC(doc, S, k, t).promise.state = "pending"
            BY <2>1, <2>2, <2>3, ShapeBodyC
        <2>5. CASE S = {}
            <3>1. ImgC(doc, S, t) = doc
                BY <2>5 DEF ImgC
            <3>2. ImgC(doc, S, t)[k] = doc[k]
                BY <1>2, <3>1, Zenon
            <3>3. QED
                BY <2>3, <3>2, Zenon
        <2>6. CASE S # {}
            <3> DEFINE im == [ j \in DOMAIN doc |-> BodyC(doc, S, j, t) ]
            <3>1. ImgC(doc, S, t) = im
                BY <2>6 DEF ImgC, im
            <3>2. DOMAIN im = DOMAIN doc
                BY DomCtor DEF im
            <3>3. im[k] = BodyC(doc, S, k, t)
                BY <1>2, <3>2, Zenon DEF im
            <3>4. QED
                BY <2>4, <3>1, <3>3, Zenon
        <2>7. QED
            BY <2>5, <2>6
    <1>3. QED
        BY <1>1, <1>2, Z3

(* A due promise fulfills its task, so a suspended task that remains was
   not due, and it still has a pending promise. *)
LEMMA ShapeSuspend ==
    ASSUME NEW obj, NEW t,
           obj.task.state = "suspended" => obj.promise.state = "pending"
    PROVE  P!Project(obj, t).task.state = "suspended" =>
               P!Project(obj, t).promise.state = "pending"
PROOF
    <1>1. CASE obj.promise.state = "pending" /\ obj.promise.timeoutAt <= t
        <2> DEFINE p == P!Project(obj, t)
        <2> DEFINE ts == IF obj.task.state = "none" THEN "none" ELSE "fulfilled"
        <2> DEFINE task1 ==
                [obj.task EXCEPT !.state          = ts,
                                 !.pid            = NoPid,
                                 !.ttl            = P!NoTime,
                                 !.leaseTimeoutAt = P!NoTime,
                                 !.retryTimeoutAt = P!NoTime,
                                 !.resumes        = {}]
        <2>1. p.task = task1
            BY <1>1, Z3 DEF p, ts, task1, P!Project
        <2>2. task1.state = ts
            BY Z3 DEF task1
        <2>3. ts = "none" \/ ts = "fulfilled"
            BY Z3 DEF ts
        <2>4. p.task.state = task1.state
            BY <2>1, Z3
        <2>5. p.task.state = ts
            BY <2>2, <2>4, Z3
        <2>6. p.task.state = "none" \/ p.task.state = "fulfilled"
            BY <2>3, <2>5, Z3
        <2>7. QED
            BY <2>6, Z3 DEF p
    <1>2. CASE obj.promise.state /= "pending" \/ ~(obj.promise.timeoutAt <= t)
        <2>1. P!Project(obj, t) = obj
            BY <1>2, ProjectId
        <2>2. QED
            BY <2>1, Zenon
    <1>3. QED
        BY <1>1, <1>2

LEMMA SuspendOn ==
    ASSUME NEW doc, NEW t, NEW S,
           S \subseteq DOMAIN doc,
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  \A k \in DOMAIN Image(doc, S, t) :
               Image(doc, S, t)[k].task.state = "suspended" =>
                   Image(doc, S, t)[k].promise.state = "pending"
PROOF
    <1>1. DOMAIN Image(doc, S, t) = DOMAIN doc
        BY ImageDom
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  Image(doc, S, t)[k].task.state = "suspended" =>
                     Image(doc, S, t)[k].promise.state = "pending"
        <2>1. /\ k \in DOMAIN Image(doc, S, t)
              /\ Image(doc, S, t)[k]
                    = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
            BY <1>2, ImageVal
        <2>2. CASE k \in S
            <3>1. Image(doc, S, t)[k] = P!Project(doc[k], t)
                BY <2>1, <2>2
            <3>2. doc[k].task.state = "suspended" =>
                      doc[k].promise.state = "pending"
                BY <1>2, Zenon
            <3>3. P!Project(doc[k], t).task.state = "suspended" =>
                      P!Project(doc[k], t).promise.state = "pending"
                BY <3>2, ShapeSuspend
            <3>4. QED
                BY <3>1, <3>3, Zenon
        <2>3. CASE k \notin S
            <3>1. Image(doc, S, t)[k] = doc[k]
                BY <2>1, <2>3
            <3>2. QED
                BY <1>2, <3>1, Zenon
        <2>4. QED
            BY <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2, Z3

LEMMA PromiseGuard ==
    ASSUME NEW a, NEW b, NEW t,
           P!Project(a, t) = a,
           b.promise.state = a.promise.state,
           b.promise.timeoutAt = a.promise.timeoutAt
    PROVE  P!Project(b, t) = b
PROOF
    <1>1. \/ a.promise.state /= "pending"
          \/ ~(a.promise.timeoutAt <= t)
        BY GuardHeld
    <1>2. \/ b.promise.state /= "pending"
          \/ ~(b.promise.timeoutAt <= t)
        BY <1>1, Zenon
    <1>3. QED
        BY <1>2, ProjectId

LEMMA ProjectWake ==
    ASSUME NEW obj, NEW srcs, NEW t,
           P!Project(obj, t) = obj
    PROVE  P!Project(Woken(obj, srcs, t), t) = Woken(obj, srcs, t)
PROOF
    <1> DEFINE w == Woken(obj, srcs, t)
    <1>1. CASE srcs = {}
        <2>1. w = obj
            BY <1>1, Z3 DEF w, Woken
        <2>2. QED
            BY <2>1, Zenon DEF w
    <1>2. CASE srcs # {} /\ obj.task.state \in {"none", "fulfilled"}
        <2>1. w = obj
            BY <1>2, Z3 DEF w, Woken
        <2>2. QED
            BY <2>1, Zenon DEF w
    <1>3. CASE srcs # {} /\ obj.task.state = "suspended"
        <2> DEFINE wk == P!WakeSuspended(obj, srcs, t)
        <2>1. w = wk
            BY <1>3, Z3 DEF w, Woken, wk
        <2>2. wk.promise = obj.promise
            BY Z3 DEF wk, P!WakeSuspended
        <2>3. /\ wk.promise.state = obj.promise.state
              /\ wk.promise.timeoutAt = obj.promise.timeoutAt
            BY <2>2, Z3
        <2>4. P!Project(wk, t) = wk
            BY <2>3, PromiseGuard DEF wk
        <2>5. QED
            BY <2>1, <2>4, Zenon DEF w, wk
    <1>4. CASE srcs # {} /\ obj.task.state \notin {"none", "fulfilled"}
                       /\ obj.task.state /= "suspended"
        <2> DEFINE un == P!UnionResumes(obj, srcs)
        <2>1. w = un
            BY <1>4, Z3 DEF w, Woken, un
        <2>2. un.promise = obj.promise
            BY Z3 DEF un, P!UnionResumes
        <2>3. /\ un.promise.state = obj.promise.state
              /\ un.promise.timeoutAt = obj.promise.timeoutAt
            BY <2>2, Z3
        <2>4. P!Project(un, t) = un
            BY <2>3, PromiseGuard DEF un
        <2>5. QED
            BY <2>1, <2>4, Zenon DEF w, un
    <1>5. QED
        BY <1>1, <1>2, <1>3, <1>4

LEMMA ProjectCleared ==
    ASSUME NEW doc, NEW S, NEW j, NEW t,
           P!Project(doc[j], t) = doc[j]
    PROVE  P!Project(Cleared(doc, S, j), t) = Cleared(doc, S, j)
PROOF
    <1> DEFINE g == Drp(j, S)
    <1> DEFINE c == Cleared(doc, S, j)
    <1>1. c = (IF g = {} THEN doc[j] ELSE P!WithoutCallbacks(doc[j], g))
        BY DEF c, Cleared, g
    <1>2. CASE g = {}
        <2>1. c = doc[j]
            BY <1>1, <1>2, Z3 DEF c
        <2>2. QED
            BY <2>1, Zenon DEF c
    <1>3. CASE g # {}
        <2> DEFINE u == P!WithoutCallbacks(doc[j], g)
        <2>1. c = u
            BY <1>1, <1>3, Z3 DEF c, u
        <2>2. P!Project(u, t) = u
            BY ProjectClear DEF u
        <2>3. QED
            BY <2>1, <2>2, Zenon DEF c
    <1>4. QED
        BY <1>2, <1>3

LEMMA ProjectBodyC ==
    ASSUME NEW doc, NEW S, NEW j, NEW t,
           P!Project(doc[j], t) = doc[j]
    PROVE  P!Project(BodyC(doc, S, j, t), t) = BodyC(doc, S, j, t)
PROOF
    <1> DEFINE c == Cleared(doc, S, j)
    <1> DEFINE srcs == Src(j, S)
    <1> DEFINE b == BodyC(doc, S, j, t)
    <1>1. P!Project(c, t) = c
        BY ProjectCleared DEF c
    <1>2. P!Project(Woken(c, srcs, t), t) = Woken(c, srcs, t)
        BY <1>1, ProjectWake DEF c, srcs
    <1>3. b = Woken(c, srcs, t)
        BY DEF b, BodyC, c, srcs
    <1>4. QED
        BY <1>2, <1>3, Zenon DEF b

LEMMA FixedImgN ==
    ASSUME NEW doc, NEW t, NEW Q,
           \A k \in DOMAIN doc : P!Project(doc[k], t) = doc[k]
    PROVE  \A k \in DOMAIN ImgN(doc, Q) :
               P!Project(ImgN(doc, Q)[k], t) = ImgN(doc, Q)[k]
PROOF
    <1>1. DOMAIN ImgN(doc, Q) = DOMAIN doc
        BY DomImgN
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  P!Project(ImgN(doc, Q)[k], t) = ImgN(doc, Q)[k]
        <2> DEFINE obj == doc[k]
        <2>1. obj = doc[k] /\ P!Project(obj, t) = obj
            BY <1>2, Zenon DEF obj
        <2>2. /\ k \in DOMAIN ImgN(doc, Q)
              /\ P!Project(ImgN(doc, Q)[k], t) = ImgN(doc, Q)[k]
            BY <1>2, <2>1, StillFixed DEF obj
        <2>3. QED
            BY <2>2, Zenon
    <1>3. QED
        BY <1>1, <1>2, Z3

LEMMA FixedImgC ==
    ASSUME NEW doc, NEW S, NEW t,
           \A k \in DOMAIN doc : P!Project(doc[k], t) = doc[k]
    PROVE  \A k \in DOMAIN ImgC(doc, S, t) :
               P!Project(ImgC(doc, S, t)[k], t) = ImgC(doc, S, t)[k]
PROOF
    <1>1. DOMAIN ImgC(doc, S, t) = DOMAIN doc
        BY DomImgC
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  P!Project(ImgC(doc, S, t)[k], t) = ImgC(doc, S, t)[k]
        <2>1. P!Project(doc[k], t) = doc[k]
            BY <1>2, Zenon
        <2>2. P!Project(BodyC(doc, S, k, t), t) = BodyC(doc, S, k, t)
            BY <2>1, ProjectBodyC
        <2>3. CASE S = {}
            <3>1. ImgC(doc, S, t) = doc
                BY <2>3 DEF ImgC
            <3>2. ImgC(doc, S, t)[k] = doc[k]
                BY <1>2, <3>1, Zenon
            <3>3. QED
                BY <2>1, <3>2, Zenon
        <2>4. CASE S # {}
            <3> DEFINE im == [ j \in DOMAIN doc |-> BodyC(doc, S, j, t) ]
            <3>1. ImgC(doc, S, t) = im
                BY <2>4 DEF ImgC, im
            <3>2. DOMAIN im = DOMAIN doc
                BY DomCtor DEF im
            <3>3. im[k] = BodyC(doc, S, k, t)
                BY <1>2, <3>2, Zenon DEF im
            <3>4. QED
                BY <2>2, <3>1, <3>3, Zenon
        <2>5. QED
            BY <2>3, <2>4
    <1>3. QED
        BY <1>1, <1>2, Z3

(* The timeout image is already projected, and listeners and callbacks
   keep each object equal to its projection. *)
LEMMA FixedPass ==
    ASSUME NEW doc, NEW t, NEW S, NEW Q, NEW C,
           S = { i \in DOMAIN doc :
                   doc[i].promise.state = "pending"
                   /\ doc[i].promise.timeoutAt <= t }
    PROVE  \A k \in DOMAIN ImgC(ImgN(Image(doc, S, t), Q), C, t) :
               P!Project(ImgC(ImgN(Image(doc, S, t), Q), C, t)[k], t)
                  = ImgC(ImgN(Image(doc, S, t), Q), C, t)[k]
PROOF
    <1> DEFINE im == Image(doc, S, t)
    <1> DEFINE ln == ImgN(im, Q)
    <1> DEFINE cb == ImgC(ln, C, t)
    <1>1. \A k \in DOMAIN doc : P!Project(im[k], t) = im[k]
        BY SliceFixed DEF im
    <1>2. S \subseteq DOMAIN doc
        BY Zenon
    <1>3. DOMAIN im = DOMAIN doc
        BY <1>2, ImageDom DEF im
    <1>4. \A k \in DOMAIN im : P!Project(im[k], t) = im[k]
        BY <1>1, <1>3, Z3 DEF im
    <1>5. \A k \in DOMAIN ln : P!Project(ln[k], t) = ln[k]
        BY <1>4, FixedImgN DEF ln
    <1>6. QED
        BY <1>5, FixedImgC DEF ln, cb

LEMMA LeasePass ==
    ASSUME NEW doc, NEW t, NEW S, NEW Q, NEW C,
           S \subseteq DOMAIN doc,
           t /= NoTime,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  \A k \in DOMAIN ImgC(ImgN(Image(doc, S, t), Q), C, t) :
               ImgC(ImgN(Image(doc, S, t), Q), C, t)[k].task.state = "acquired" =>
                   /\ ImgC(ImgN(Image(doc, S, t), Q), C, t)[k].task.leaseTimeoutAt /= NoTime
                   /\ ImgC(ImgN(Image(doc, S, t), Q), C, t)[k].promise.state = "pending"
PROOF
    <1> DEFINE im == Image(doc, S, t)
    <1> DEFINE ln == ImgN(im, Q)
    <1> DEFINE cb == ImgC(ln, C, t)
    <1>1. \A k \in DOMAIN im :
              im[k].task.state = "acquired" =>
                  /\ im[k].task.leaseTimeoutAt /= NoTime
                  /\ im[k].promise.state = "pending"
        BY LeaseOn DEF im
    <1>2. \A k \in DOMAIN im :
              im[k].task.state = "pending" =>
                  /\ im[k].task.retryTimeoutAt /= NoTime
                  /\ im[k].promise.state = "pending"
        BY RetryOn DEF im
    <1>3. \A k \in DOMAIN im :
              im[k].task.state = "suspended" =>
                  im[k].promise.state = "pending"
        BY SuspendOn DEF im
    <1>4. \A k \in DOMAIN ln :
              ln[k].task.state = "acquired" =>
                  /\ ln[k].task.leaseTimeoutAt /= NoTime
                  /\ ln[k].promise.state = "pending"
        BY <1>1, <1>2, <1>3, LeaseN DEF ln
    <1>5. \A k \in DOMAIN ln :
              ln[k].task.state = "pending" =>
                  /\ ln[k].task.retryTimeoutAt /= NoTime
                  /\ ln[k].promise.state = "pending"
        BY <1>1, <1>2, <1>3, RetryN DEF ln
    <1>6. \A k \in DOMAIN ln :
              ln[k].task.state = "suspended" =>
                  ln[k].promise.state = "pending"
        BY <1>1, <1>2, <1>3, SuspendN DEF ln
    <1>7. QED
        BY <1>4, <1>5, <1>6, LeaseC DEF ln, cb

LEMMA RetryPass ==
    ASSUME NEW doc, NEW t, NEW S, NEW Q, NEW C,
           S \subseteq DOMAIN doc,
           t /= NoTime,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  \A k \in DOMAIN ImgC(ImgN(Image(doc, S, t), Q), C, t) :
               ImgC(ImgN(Image(doc, S, t), Q), C, t)[k].task.state = "pending" =>
                   /\ ImgC(ImgN(Image(doc, S, t), Q), C, t)[k].task.retryTimeoutAt /= NoTime
                   /\ ImgC(ImgN(Image(doc, S, t), Q), C, t)[k].promise.state = "pending"
PROOF
    <1> DEFINE im == Image(doc, S, t)
    <1> DEFINE ln == ImgN(im, Q)
    <1> DEFINE cb == ImgC(ln, C, t)
    <1>1. \A k \in DOMAIN im :
              im[k].task.state = "acquired" =>
                  /\ im[k].task.leaseTimeoutAt /= NoTime
                  /\ im[k].promise.state = "pending"
        BY LeaseOn DEF im
    <1>2. \A k \in DOMAIN im :
              im[k].task.state = "pending" =>
                  /\ im[k].task.retryTimeoutAt /= NoTime
                  /\ im[k].promise.state = "pending"
        BY RetryOn DEF im
    <1>3. \A k \in DOMAIN im :
              im[k].task.state = "suspended" =>
                  im[k].promise.state = "pending"
        BY SuspendOn DEF im
    <1>4. \A k \in DOMAIN ln :
              ln[k].task.state = "acquired" =>
                  /\ ln[k].task.leaseTimeoutAt /= NoTime
                  /\ ln[k].promise.state = "pending"
        BY <1>1, <1>2, <1>3, LeaseN DEF ln
    <1>5. \A k \in DOMAIN ln :
              ln[k].task.state = "pending" =>
                  /\ ln[k].task.retryTimeoutAt /= NoTime
                  /\ ln[k].promise.state = "pending"
        BY <1>1, <1>2, <1>3, RetryN DEF ln
    <1>6. \A k \in DOMAIN ln :
              ln[k].task.state = "suspended" =>
                  ln[k].promise.state = "pending"
        BY <1>1, <1>2, <1>3, SuspendN DEF ln
    <1>7. QED
        BY <1>4, <1>5, <1>6, RetryC DEF ln, cb

LEMMA SuspendPass ==
    ASSUME NEW doc, NEW t, NEW S, NEW Q, NEW C,
           S \subseteq DOMAIN doc,
           t /= NoTime,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  \A k \in DOMAIN ImgC(ImgN(Image(doc, S, t), Q), C, t) :
               ImgC(ImgN(Image(doc, S, t), Q), C, t)[k].task.state = "suspended" =>
                   ImgC(ImgN(Image(doc, S, t), Q), C, t)[k].promise.state = "pending"
PROOF
    <1> DEFINE im == Image(doc, S, t)
    <1> DEFINE ln == ImgN(im, Q)
    <1> DEFINE cb == ImgC(ln, C, t)
    <1>1. \A k \in DOMAIN im :
              im[k].task.state = "acquired" =>
                  /\ im[k].task.leaseTimeoutAt /= NoTime
                  /\ im[k].promise.state = "pending"
        BY LeaseOn DEF im
    <1>2. \A k \in DOMAIN im :
              im[k].task.state = "pending" =>
                  /\ im[k].task.retryTimeoutAt /= NoTime
                  /\ im[k].promise.state = "pending"
        BY RetryOn DEF im
    <1>3. \A k \in DOMAIN im :
              im[k].task.state = "suspended" =>
                  im[k].promise.state = "pending"
        BY SuspendOn DEF im
    <1>4. \A k \in DOMAIN ln :
              ln[k].task.state = "acquired" =>
                  /\ ln[k].task.leaseTimeoutAt /= NoTime
                  /\ ln[k].promise.state = "pending"
        BY <1>1, <1>2, <1>3, LeaseN DEF ln
    <1>5. \A k \in DOMAIN ln :
              ln[k].task.state = "pending" =>
                  /\ ln[k].task.retryTimeoutAt /= NoTime
                  /\ ln[k].promise.state = "pending"
        BY <1>1, <1>2, <1>3, RetryN DEF ln
    <1>6. \A k \in DOMAIN ln :
              ln[k].task.state = "suspended" =>
                  ln[k].promise.state = "pending"
        BY <1>1, <1>2, <1>3, SuspendN DEF ln
    <1>7. QED
        BY <1>4, <1>5, <1>6, SuspendC DEF ln, cb

(* A slice that agrees with the store still agrees after the timeout image. *)
LEMMA AgreeImage ==
    ASSUME NEW base, NEW doc, NEW t, NEW S,
           DOMAIN doc \subseteq DOMAIN base,
           S \subseteq DOMAIN doc,
           \A k \in DOMAIN doc : base[k] = doc[k]
    PROVE  \A k \in DOMAIN Image(doc, S, t) :
               Image(base, S, t)[k] = Image(doc, S, t)[k]
PROOF
    <1>1. DOMAIN Image(doc, S, t) = DOMAIN doc
        BY ImageDom
    <1>2. S \subseteq DOMAIN base
        BY Zenon
    <1>3. ASSUME NEW k \in DOMAIN doc
          PROVE  Image(base, S, t)[k] = Image(doc, S, t)[k]
        <2>1. base[k] = doc[k]
            BY <1>3, Zenon
        <2>2. k \in DOMAIN base
            BY <1>3, Zenon
        <2>3. /\ k \in DOMAIN Image(doc, S, t)
              /\ Image(doc, S, t)[k]
                    = IF k \in S THEN P!Project(doc[k], t) ELSE doc[k]
            BY <1>3, ImageVal
        <2>4. /\ k \in DOMAIN Image(base, S, t)
              /\ Image(base, S, t)[k]
                    = IF k \in S THEN P!Project(base[k], t) ELSE base[k]
            BY <1>2, <2>2, ImageVal
        <2>5. P!Project(base[k], t) = P!Project(doc[k], t)
            BY <2>1, Zenon
        <2>6. QED
            BY <2>1, <2>3, <2>4, <2>5, Z3
    <1>4. QED
        BY <1>1, <1>3, Z3

LEMMA AgreeImgN ==
    ASSUME NEW base, NEW doc, NEW Q,
           DOMAIN doc \subseteq DOMAIN base,
           \A k \in DOMAIN doc : base[k] = doc[k]
    PROVE  \A k \in DOMAIN ImgN(doc, Q) :
               ImgN(base, Q)[k] = ImgN(doc, Q)[k]
PROOF
    <1>1. DOMAIN ImgN(doc, Q) = DOMAIN doc
        BY DomImgN
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  ImgN(base, Q)[k] = ImgN(doc, Q)[k]
        <2>1. base[k] = doc[k]
            BY <1>2, Zenon
        <2>2. k \in DOMAIN base
            BY <1>2, Zenon
        <2>3. CASE Q = {}
            <3>1. ImgN(base, Q) = base /\ ImgN(doc, Q) = doc
                BY <2>3 DEF ImgN
            <3>2. QED
                BY <2>1, <2>2, <3>1, Zenon
        <2>4. CASE Q # {}
            <3> DEFINE bB == [ j \in DOMAIN base |-> BodyN(base, Q, j) ]
            <3> DEFINE bD == [ j \in DOMAIN doc |-> BodyN(doc, Q, j) ]
            <3>1. ImgN(base, Q) = bB /\ ImgN(doc, Q) = bD
                BY <2>4 DEF ImgN, bB, bD
            <3>2. DOMAIN bB = DOMAIN base /\ DOMAIN bD = DOMAIN doc
                BY DomCtor DEF bB, bD
            <3>3. bB[k] = BodyN(base, Q, k)
                BY <2>2, <3>2, Zenon DEF bB
            <3>4. bD[k] = BodyN(doc, Q, k)
                BY <1>2, <3>2, Zenon DEF bD
            <3>5. BodyN(base, Q, k) = BodyN(doc, Q, k)
                BY <2>1, SameBody
            <3>6. QED
                BY <3>1, <3>3, <3>4, <3>5, Zenon
        <2>5. QED
            BY <2>3, <2>4
    <1>3. QED
        BY <1>1, <1>2, Z3

LEMMA AgreeImgC ==
    ASSUME NEW base, NEW doc, NEW S, NEW t,
           DOMAIN doc \subseteq DOMAIN base,
           \A k \in DOMAIN doc : base[k] = doc[k]
    PROVE  \A k \in DOMAIN ImgC(doc, S, t) :
               ImgC(base, S, t)[k] = ImgC(doc, S, t)[k]
PROOF
    <1>1. DOMAIN ImgC(doc, S, t) = DOMAIN doc
        BY DomImgC
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  ImgC(base, S, t)[k] = ImgC(doc, S, t)[k]
        <2>1. base[k] = doc[k]
            BY <1>2, Zenon
        <2>2. k \in DOMAIN base
            BY <1>2, Zenon
        <2>3. CASE S = {}
            <3>1. ImgC(base, S, t) = base /\ ImgC(doc, S, t) = doc
                BY <2>3 DEF ImgC
            <3>2. QED
                BY <2>1, <2>2, <3>1, Zenon
        <2>4. CASE S # {}
            <3> DEFINE bB == [ j \in DOMAIN base |-> BodyC(base, S, j, t) ]
            <3> DEFINE bD == [ j \in DOMAIN doc |-> BodyC(doc, S, j, t) ]
            <3>1. ImgC(base, S, t) = bB /\ ImgC(doc, S, t) = bD
                BY <2>4 DEF ImgC, bB, bD
            <3>2. DOMAIN bB = DOMAIN base /\ DOMAIN bD = DOMAIN doc
                BY DomCtor DEF bB, bD
            <3>3. bB[k] = BodyC(base, S, k, t)
                BY <2>2, <3>2, Zenon DEF bB
            <3>4. bD[k] = BodyC(doc, S, k, t)
                BY <1>2, <3>2, Zenon DEF bD
            <3>5. BodyC(base, S, k, t) = BodyC(doc, S, k, t)
                BY <2>1, SameBodyC
            <3>6. QED
                BY <3>1, <3>3, <3>4, <3>5, Zenon
        <2>5. QED
            BY <2>3, <2>4
    <1>3. QED
        BY <1>1, <1>2, Z3

(* Timeouts, listeners, and callbacks, then the due leases of that
   document. The outbox is still the listener outbox. *)
LEMMA LeaseJoin ==
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
               y.awaiter \in DOMAIN base => y.awaiter \in DOMAIN doc,
           t /= NoTime,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  ReachN(base, box, t,
                  ImgL(ImgC(ImgN(Image(base, S, t),
                                 DueN(Image(doc, S, t), t)),
                            DueC(ImgN(Image(doc, S, t),
                                      DueN(Image(doc, S, t), t)), t),
                            t),
                       { i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                DueN(Image(doc, S, t), t)),
                                          DueC(ImgN(Image(doc, S, t),
                                                    DueN(Image(doc, S, t), t)),
                                               t),
                                          t) :
                           ImgC(ImgN(Image(doc, S, t),
                                     DueN(Image(doc, S, t), t)),
                                DueC(ImgN(Image(doc, S, t),
                                          DueN(Image(doc, S, t), t)), t),
                                t)[i].task.state = "acquired"
                           /\ ImgC(ImgN(Image(doc, S, t),
                                        DueN(Image(doc, S, t), t)),
                                   DueC(ImgN(Image(doc, S, t),
                                             DueN(Image(doc, S, t), t)), t),
                                   t)[i].task.leaseTimeoutAt <= t },
                       t),
                  BoxN(box, Image(base, S, t), DueN(Image(doc, S, t), t), t),
                  Cardinality(S)
                    + Cardinality(DueN(Image(doc, S, t), t))
                    + Cardinality(DueC(ImgN(Image(doc, S, t),
                                            DueN(Image(doc, S, t), t)), t))
                    + Cardinality({ i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                           DueN(Image(doc, S, t), t)),
                                                     DueC(ImgN(Image(doc, S, t),
                                                               DueN(Image(doc, S, t), t)),
                                                          t),
                                                     t) :
                                      ImgC(ImgN(Image(doc, S, t),
                                                DueN(Image(doc, S, t), t)),
                                           DueC(ImgN(Image(doc, S, t),
                                                     DueN(Image(doc, S, t), t)), t),
                                           t)[i].task.state = "acquired"
                                      /\ ImgC(ImgN(Image(doc, S, t),
                                                   DueN(Image(doc, S, t), t)),
                                              DueC(ImgN(Image(doc, S, t),
                                                        DueN(Image(doc, S, t), t)),
                                                 t),
                                              t)[i].task.leaseTimeoutAt <= t }))
PROOF
    <1> DEFINE imB == Image(base, S, t)
    <1> DEFINE imD == Image(doc, S, t)
    <1> DEFINE pairs == DueN(imD, t)
    <1> DEFINE docL == ImgN(imD, pairs)
    <1> DEFINE mid == ImgN(imB, pairs)
    <1> DEFINE boxL == BoxN(box, imB, pairs, t)
    <1> DEFINE calls == DueC(docL, t)
    <1> DEFINE cbB == ImgC(mid, calls, t)
    <1> DEFINE cbD == ImgC(docL, calls, t)
    <1> DEFINE exp ==
            { i \in DOMAIN cbD :
                cbD[i].task.state = "acquired"
                /\ cbD[i].task.leaseTimeoutAt <= t }
    <1> DEFINE n3 ==
            Cardinality(S) + Cardinality(pairs) + Cardinality(calls)
    <1>1. DOMAIN doc \subseteq DOMAIN base /\ DOMAIN doc \subseteq Id
        BY Zenon
    <1>2. S \subseteq DOMAIN doc
        BY Zenon
    <1>3. S \subseteq DOMAIN base
        BY <1>1, <1>2, Zenon
    <1>4. DOMAIN imD = DOMAIN doc /\ DOMAIN imB = DOMAIN base
        BY <1>2, <1>3, ImageDom DEF imD, imB
    <1>5. DOMAIN docL = DOMAIN imD /\ DOMAIN mid = DOMAIN imB
        BY DomImgN DEF docL, mid, imD, imB, pairs
    <1>6. DOMAIN cbD = DOMAIN docL /\ DOMAIN cbB = DOMAIN mid
        BY DomImgC DEF cbD, cbB, docL, mid, calls
    <1>7. DOMAIN cbD \subseteq DOMAIN cbB /\ DOMAIN cbD \subseteq Id
        BY <1>1, <1>4, <1>5, <1>6, Zenon DEF cbD, cbB
    <1>8. \A k \in DOMAIN imD : imB[k] = imD[k]
        BY <1>1, <1>2, AgreeImage DEF imB, imD
    <1>9. DOMAIN imD \subseteq DOMAIN imB
        BY <1>1, <1>4, Zenon DEF imD, imB
    <1>10. \A k \in DOMAIN docL : mid[k] = docL[k]
        BY <1>8, <1>9, AgreeImgN DEF imB, imD, docL, mid, pairs
    <1>11. DOMAIN docL \subseteq DOMAIN mid
        BY <1>1, <1>4, <1>5, Zenon DEF docL, mid
    <1>12. \A k \in DOMAIN cbD : cbB[k] = cbD[k]
        BY <1>10, <1>11, AgreeImgC DEF mid, docL, cbB, cbD, calls
    <1>13. \A k \in DOMAIN cbD : P!Project(cbD[k], t) = cbD[k]
        BY FixedPass DEF imD, pairs, docL, calls, cbD
    <1>14. \A k \in DOMAIN cbD :
              cbD[k].task.state = "acquired" =>
                  /\ cbD[k].task.leaseTimeoutAt /= NoTime
                  /\ cbD[k].promise.state = "pending"
        BY <1>2, LeasePass DEF imD, pairs, docL, calls, cbD
    <1>15. ReachN(base, box, t, cbB, boxL, n3)
        BY ThreePass DEF imB, imD, pairs, docL, mid, boxL, calls, cbB, n3
    <1>16. ReachN(cbB, boxL, t, ImgL(cbB, exp, t), boxL, Cardinality(exp))
        BY <1>7, <1>12, <1>13, <1>14, LeaseFrom DEF cbB, cbD, boxL, exp
    <1>17. Cardinality(S) \in Nat
        <2>1. Cardinality(S) \in 0 .. P!MaxSweep
            BY TimeoutChain
        <2>2. P!MaxSweep \in Nat
            BY SweepCap
        <2>3. QED
            BY <2>1, <2>2, Z3
    <1>18. Cardinality(pairs) \in Nat
        <2>1. DOMAIN imD \subseteq Id
            BY <1>1, <1>4, Zenon DEF imD
        <2>2. IsFiniteSet(pairs)
            BY <2>1, PairFinite DEF pairs, imD
        <2>3. QED
            BY <2>2, FS_CardinalityType
    <1>19. Cardinality(calls) \in Nat
        <2>1. DOMAIN docL \subseteq Id
            BY <1>1, <1>4, <1>5, Zenon DEF docL, imD
        <2>2. IsFiniteSet(calls)
            BY <2>1, AwFinite DEF calls, docL
        <2>3. QED
            BY <2>2, FS_CardinalityType
    <1>20. n3 \in Nat
        BY <1>17, <1>18, <1>19, Z3 DEF n3
    <1>21. Cardinality(exp) \in Nat
        <2>1. exp \subseteq DOMAIN cbD
            BY ONLY Zenon DEF exp
        <2>2. exp \subseteq Id
            BY ONLY <1>7, <2>1, Zenon
        <2>3. IsFiniteSet(exp) /\ Cardinality(exp) \in 0 .. P!MaxSweep
            BY ONLY <2>2, SubCap
        <2>4. IsFiniteSet(exp)
            BY ONLY <2>3, Zenon
        <2>5. QED
            BY ONLY <2>4, FS_CardinalityType
    <1>22. ReachN(base, box, t, ImgL(cbB, exp, t), boxL, n3 + Cardinality(exp))
        BY <1>15, <1>16, <1>20, <1>21, ReachCat DEF cbB, boxL, exp, n3
    <1>23. QED
        BY <1>22 DEF imB, imD, pairs, docL, mid, calls, cbB, cbD, boxL, exp, n3

LEMMA DomImgL ==
    ASSUME NEW doc, NEW T, NEW t
    PROVE  DOMAIN ImgL(doc, T, t) = DOMAIN doc
PROOF
    <1>1. CASE T = {}
        BY <1>1 DEF ImgL
    <1>2. CASE T # {}
        <2> DEFINE im ==
                [ i \in DOMAIN doc |->
                    IF i \in T THEN LeaseBody(doc[i], t) ELSE doc[i] ]
        <2>1. ImgL(doc, T, t) = im
            BY <1>2 DEF ImgL, im
        <2>2. DOMAIN im = DOMAIN doc
            BY DomCtor DEF im
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2

LEMMA LeaseIn ==
    ASSUME NEW o, NEW T, NEW t, NEW x,
           x \in DOMAIN o, x \in T, T \subseteq DOMAIN o
    PROVE  ImgL(o, T, t)[x] = LeaseBody(o[x], t)
PROOF
    <1>1. T # {}
        BY Z3
    <1> DEFINE body ==
            [ i \in DOMAIN o |-> IF i \in T THEN LeaseBody(o[i], t) ELSE o[i] ]
    <1>2. ImgL(o, T, t) = body
        BY <1>1 DEF ImgL, body
    <1>3. DOMAIN body = DOMAIN o
        BY DomCtor DEF body
    <1>4. body[x] = (IF x \in T THEN LeaseBody(o[x], t) ELSE o[x])
        BY Zenon DEF body
    <1>5. body[x] = LeaseBody(o[x], t)
        BY Z3
    <1>6. QED
        BY <1>2, <1>3, <1>4, <1>5, Zenon

LEMMA SameLease ==
    ASSUME NEW a, NEW b, NEW t, a = b
    PROVE  LeaseBody(a, t) = LeaseBody(b, t)
PROOF
    <1>1. a = b
        OBVIOUS
    <1>2. QED
        BY ONLY <1>1, Isa DEF LeaseBody

(* Expiring a lease makes the task pending at this time and keeps the promise. *)
LEMMA LeaseKeeps ==
    ASSUME NEW obj, NEW t
    PROVE  /\ LeaseBody(obj, t).task.state = "pending"
           /\ LeaseBody(obj, t).task.retryTimeoutAt = t
           /\ LeaseBody(obj, t).promise.state = obj.promise.state
           /\ LeaseBody(obj, t).promise.timeoutAt = obj.promise.timeoutAt
PROOF
    <1> DEFINE task1 ==
            [obj.task EXCEPT !.state          = "pending",
                             !.pid            = NoPid,
                             !.ttl            = NoTime,
                             !.leaseTimeoutAt = NoTime,
                             !.retryTimeoutAt = t]
    <1> DEFINE body == [obj EXCEPT !.task = task1]
    <1>1. task1.state = "pending"
        BY Z3 DEF task1
    <1>2. task1.retryTimeoutAt = t
        BY Z3 DEF task1
    <1>3. body.task = task1
        BY Z3 DEF body
    <1>4. body.promise = obj.promise
        BY Z3 DEF body
    <1>5. LeaseBody(obj, t) = body
        BY ONLY Zenon DEF LeaseBody, task1, body
    <1>6. LeaseBody(obj, t).task.state = "pending"
        BY <1>1, <1>3, <1>5, Zenon DEF body, task1
    <1>7. LeaseBody(obj, t).task.retryTimeoutAt = t
        BY <1>2, <1>3, <1>5, Zenon DEF body, task1
    <1>8. LeaseBody(obj, t).promise.state = obj.promise.state
        BY <1>4, <1>5, Z3 DEF body
    <1>9. LeaseBody(obj, t).promise.timeoutAt = obj.promise.timeoutAt
        BY <1>4, <1>5, Z3 DEF body
    <1>10. QED
        BY <1>6, <1>7, <1>8, <1>9

LEMMA RetryImgL ==
    ASSUME NEW doc, NEW T, NEW t,
           T \subseteq DOMAIN doc,
           t /= NoTime,
           \A k \in T : doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending"
    PROVE  \A k \in DOMAIN ImgL(doc, T, t) :
               ImgL(doc, T, t)[k].task.state = "pending" =>
                   /\ ImgL(doc, T, t)[k].task.retryTimeoutAt /= NoTime
                   /\ ImgL(doc, T, t)[k].promise.state = "pending"
PROOF
    <1>1. DOMAIN ImgL(doc, T, t) = DOMAIN doc
        BY DomImgL
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  ImgL(doc, T, t)[k].task.state = "pending" =>
                     /\ ImgL(doc, T, t)[k].task.retryTimeoutAt /= NoTime
                     /\ ImgL(doc, T, t)[k].promise.state = "pending"
        <2>1. CASE k \notin T
            <3>1. ImgL(doc, T, t)[k] = doc[k]
                BY <1>2, <2>1, LeaseAt
            <3>2. QED
                BY <1>2, <3>1, Zenon
        <2>2. CASE k \in T
            <3> DEFINE b == LeaseBody(doc[k], t)
            <3>1. ImgL(doc, T, t)[k] = b
                BY <1>2, <2>2, LeaseIn DEF b
            <3>2. doc[k].promise.state = "pending"
                BY <2>2, Zenon
            <3>3. /\ b.task.state = "pending"
                  /\ b.task.retryTimeoutAt = t
                  /\ b.promise.state = doc[k].promise.state
                BY LeaseKeeps DEF b
            <3>4. b.promise.state = "pending"
                BY <3>2, <3>3, Zenon
            <3>5. b.task.retryTimeoutAt /= NoTime
                BY <3>3, Zenon
            <3>6. QED
                BY <3>1, <3>3, <3>4, <3>5, Zenon
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2, Z3

LEMMA FixedImgL ==
    ASSUME NEW doc, NEW T, NEW t,
           T \subseteq DOMAIN doc,
           \A k \in DOMAIN doc : P!Project(doc[k], t) = doc[k]
    PROVE  \A k \in DOMAIN ImgL(doc, T, t) :
               P!Project(ImgL(doc, T, t)[k], t) = ImgL(doc, T, t)[k]
PROOF
    <1>1. DOMAIN ImgL(doc, T, t) = DOMAIN doc
        BY DomImgL
    <1>2. ASSUME NEW k \in DOMAIN doc
          PROVE  P!Project(ImgL(doc, T, t)[k], t) = ImgL(doc, T, t)[k]
        <2>1. P!Project(doc[k], t) = doc[k]
            BY <1>2, Zenon
        <2>2. CASE k \notin T
            <3>1. ImgL(doc, T, t)[k] = doc[k]
                BY <1>2, <2>2, LeaseAt
            <3>2. QED
                BY <2>1, <3>1, Zenon
        <2>3. CASE k \in T
            <3> DEFINE b == LeaseBody(doc[k], t)
            <3>1. ImgL(doc, T, t)[k] = b
                BY <1>2, <2>3, LeaseIn DEF b
            <3>2. /\ b.promise.state = doc[k].promise.state
                  /\ b.promise.timeoutAt = doc[k].promise.timeoutAt
                BY LeaseKeeps DEF b
            <3>3. P!Project(b, t) = b
                BY <2>1, <3>2, PromiseGuard DEF b
            <3>4. QED
                BY <3>1, <3>3, Zenon
        <2>4. QED
            BY <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2, Z3

LEMMA AgreeImgL ==
    ASSUME NEW base, NEW doc, NEW T, NEW t,
           DOMAIN doc \subseteq DOMAIN base,
           T \subseteq DOMAIN doc,
           \A k \in DOMAIN doc : base[k] = doc[k]
    PROVE  \A k \in DOMAIN ImgL(doc, T, t) :
               ImgL(base, T, t)[k] = ImgL(doc, T, t)[k]
PROOF
    <1>1. DOMAIN ImgL(doc, T, t) = DOMAIN doc
        BY DomImgL
    <1>2. T \subseteq DOMAIN base
        BY Zenon
    <1>3. ASSUME NEW k \in DOMAIN doc
          PROVE  ImgL(base, T, t)[k] = ImgL(doc, T, t)[k]
        <2>1. base[k] = doc[k]
            BY <1>3, Zenon
        <2>2. k \in DOMAIN base
            BY <1>3, Zenon
        <2>3. CASE k \notin T
            <3>1. ImgL(doc, T, t)[k] = doc[k]
                BY <1>3, <2>3, LeaseAt
            <3>2. ImgL(base, T, t)[k] = base[k]
                BY <1>2, <2>2, <2>3, LeaseAt
            <3>3. QED
                BY <2>1, <3>1, <3>2, Zenon
        <2>4. CASE k \in T
            <3>1. ImgL(doc, T, t)[k] = LeaseBody(doc[k], t)
                BY <1>3, <2>4, LeaseIn
            <3>2. ImgL(base, T, t)[k] = LeaseBody(base[k], t)
                BY <1>2, <2>2, <2>4, LeaseIn
            <3>3. LeaseBody(base[k], t) = LeaseBody(doc[k], t)
                BY <2>1, SameLease
            <3>4. QED
                BY <3>1, <3>2, <3>3, Zenon
        <2>5. QED
            BY <2>3, <2>4
    <1>4. QED
        BY <1>1, <1>3, Z3

(* The due retries follow the leases. Each posts its Execute on the
   listener outbox. *)
LEMMA RetryJoin ==
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
               y.awaiter \in DOMAIN base => y.awaiter \in DOMAIN doc,
           t /= NoTime,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  ReachN(base, box, t,
                  ImgR(ImgL(ImgC(ImgN(Image(base, S, t),
                                      DueN(Image(doc, S, t), t)),
                                 DueC(ImgN(Image(doc, S, t),
                                           DueN(Image(doc, S, t), t)), t),
                                 t),
                            { i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                     DueN(Image(doc, S, t), t)),
                                               DueC(ImgN(Image(doc, S, t),
                                                         DueN(Image(doc, S, t), t)),
                                                    t),
                                               t) :
                                ImgC(ImgN(Image(doc, S, t),
                                          DueN(Image(doc, S, t), t)),
                                     DueC(ImgN(Image(doc, S, t),
                                               DueN(Image(doc, S, t), t)), t),
                                     t)[i].task.state = "acquired"
                                /\ ImgC(ImgN(Image(doc, S, t),
                                             DueN(Image(doc, S, t), t)),
                                        DueC(ImgN(Image(doc, S, t),
                                                  DueN(Image(doc, S, t), t)), t),
                                        t)[i].task.leaseTimeoutAt <= t },
                            t),
                       { j \in DOMAIN ImgL(ImgC(ImgN(Image(doc, S, t),
                                                    DueN(Image(doc, S, t), t)),
                                               DueC(ImgN(Image(doc, S, t),
                                                         DueN(Image(doc, S, t), t)),
                                                    t),
                                               t),
                                          { i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                                   DueN(Image(doc, S, t), t)),
                                                             DueC(ImgN(Image(doc, S, t),
                                                                       DueN(Image(doc, S, t), t)),
                                                                  t),
                                                             t) :
                                              ImgC(ImgN(Image(doc, S, t),
                                                        DueN(Image(doc, S, t), t)),
                                                   DueC(ImgN(Image(doc, S, t),
                                                             DueN(Image(doc, S, t), t)), t),
                                                   t)[i].task.state = "acquired"
                                              /\ ImgC(ImgN(Image(doc, S, t),
                                                           DueN(Image(doc, S, t), t)),
                                                      DueC(ImgN(Image(doc, S, t),
                                                                DueN(Image(doc, S, t), t)), t),
                                                      t)[i].task.leaseTimeoutAt <= t },
                                          t) :
                           ImgL(ImgC(ImgN(Image(doc, S, t),
                                          DueN(Image(doc, S, t), t)),
                                     DueC(ImgN(Image(doc, S, t),
                                               DueN(Image(doc, S, t), t)), t),
                                     t),
                                { i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                         DueN(Image(doc, S, t), t)),
                                                   DueC(ImgN(Image(doc, S, t),
                                                             DueN(Image(doc, S, t), t)),
                                                        t),
                                                   t) :
                                    ImgC(ImgN(Image(doc, S, t),
                                              DueN(Image(doc, S, t), t)),
                                         DueC(ImgN(Image(doc, S, t),
                                                   DueN(Image(doc, S, t), t)), t),
                                         t)[i].task.state = "acquired"
                                    /\ ImgC(ImgN(Image(doc, S, t),
                                                 DueN(Image(doc, S, t), t)),
                                            DueC(ImgN(Image(doc, S, t),
                                                      DueN(Image(doc, S, t), t)), t),
                                            t)[i].task.leaseTimeoutAt <= t },
                                t)[j].task.state = "pending"
                           /\ ImgL(ImgC(ImgN(Image(doc, S, t),
                                             DueN(Image(doc, S, t), t)),
                                        DueC(ImgN(Image(doc, S, t),
                                                  DueN(Image(doc, S, t), t)), t),
                                        t),
                                   { i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                            DueN(Image(doc, S, t), t)),
                                                      DueC(ImgN(Image(doc, S, t),
                                                                DueN(Image(doc, S, t), t)),
                                                           t),
                                                      t) :
                                       ImgC(ImgN(Image(doc, S, t),
                                                 DueN(Image(doc, S, t), t)),
                                            DueC(ImgN(Image(doc, S, t),
                                                      DueN(Image(doc, S, t), t)), t),
                                            t)[i].task.state = "acquired"
                                       /\ ImgC(ImgN(Image(doc, S, t),
                                                    DueN(Image(doc, S, t), t)),
                                               DueC(ImgN(Image(doc, S, t),
                                                         DueN(Image(doc, S, t), t)), t),
                                               t)[i].task.leaseTimeoutAt <= t },
                                   t)[j].task.retryTimeoutAt <= t },
                       t),
                  BoxAt(BoxN(box, Image(base, S, t), DueN(Image(doc, S, t), t), t),
                        ImgL(ImgC(ImgN(Image(base, S, t),
                                       DueN(Image(doc, S, t), t)),
                                  DueC(ImgN(Image(doc, S, t),
                                            DueN(Image(doc, S, t), t)), t),
                                  t),
                             { i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                      DueN(Image(doc, S, t), t)),
                                                DueC(ImgN(Image(doc, S, t),
                                                          DueN(Image(doc, S, t), t)),
                                                     t),
                                                t) :
                                 ImgC(ImgN(Image(doc, S, t),
                                           DueN(Image(doc, S, t), t)),
                                      DueC(ImgN(Image(doc, S, t),
                                                DueN(Image(doc, S, t), t)), t),
                                      t)[i].task.state = "acquired"
                                 /\ ImgC(ImgN(Image(doc, S, t),
                                              DueN(Image(doc, S, t), t)),
                                         DueC(ImgN(Image(doc, S, t),
                                                   DueN(Image(doc, S, t), t)), t),
                                         t)[i].task.leaseTimeoutAt <= t },
                             t),
                        { j \in DOMAIN ImgL(ImgC(ImgN(Image(doc, S, t),
                                                     DueN(Image(doc, S, t), t)),
                                                DueC(ImgN(Image(doc, S, t),
                                                          DueN(Image(doc, S, t), t)),
                                                     t),
                                                t),
                                           { i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                                    DueN(Image(doc, S, t), t)),
                                                              DueC(ImgN(Image(doc, S, t),
                                                                        DueN(Image(doc, S, t), t)),
                                                                   t),
                                                              t) :
                                               ImgC(ImgN(Image(doc, S, t),
                                                         DueN(Image(doc, S, t), t)),
                                                    DueC(ImgN(Image(doc, S, t),
                                                              DueN(Image(doc, S, t), t)), t),
                                                    t)[i].task.state = "acquired"
                                               /\ ImgC(ImgN(Image(doc, S, t),
                                                            DueN(Image(doc, S, t), t)),
                                                       DueC(ImgN(Image(doc, S, t),
                                                                 DueN(Image(doc, S, t), t)), t),
                                                       t)[i].task.leaseTimeoutAt <= t },
                                           t) :
                            ImgL(ImgC(ImgN(Image(doc, S, t),
                                           DueN(Image(doc, S, t), t)),
                                      DueC(ImgN(Image(doc, S, t),
                                                DueN(Image(doc, S, t), t)), t),
                                      t),
                                 { i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                          DueN(Image(doc, S, t), t)),
                                                    DueC(ImgN(Image(doc, S, t),
                                                              DueN(Image(doc, S, t), t)),
                                                         t),
                                                    t) :
                                     ImgC(ImgN(Image(doc, S, t),
                                               DueN(Image(doc, S, t), t)),
                                          DueC(ImgN(Image(doc, S, t),
                                                    DueN(Image(doc, S, t), t)), t),
                                          t)[i].task.state = "acquired"
                                     /\ ImgC(ImgN(Image(doc, S, t),
                                                  DueN(Image(doc, S, t), t)),
                                             DueC(ImgN(Image(doc, S, t),
                                                       DueN(Image(doc, S, t), t)), t),
                                             t)[i].task.leaseTimeoutAt <= t },
                                 t)[j].task.state = "pending"
                            /\ ImgL(ImgC(ImgN(Image(doc, S, t),
                                              DueN(Image(doc, S, t), t)),
                                         DueC(ImgN(Image(doc, S, t),
                                                   DueN(Image(doc, S, t), t)), t),
                                         t),
                                    { i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                             DueN(Image(doc, S, t), t)),
                                                       DueC(ImgN(Image(doc, S, t),
                                                                 DueN(Image(doc, S, t), t)),
                                                            t),
                                                       t) :
                                        ImgC(ImgN(Image(doc, S, t),
                                                  DueN(Image(doc, S, t), t)),
                                             DueC(ImgN(Image(doc, S, t),
                                                       DueN(Image(doc, S, t), t)), t),
                                             t)[i].task.state = "acquired"
                                        /\ ImgC(ImgN(Image(doc, S, t),
                                                     DueN(Image(doc, S, t), t)),
                                                DueC(ImgN(Image(doc, S, t),
                                                          DueN(Image(doc, S, t), t)), t),
                                                t)[i].task.leaseTimeoutAt <= t },
                                    t)[j].task.retryTimeoutAt <= t }),
                  Cardinality(S)
                    + Cardinality(DueN(Image(doc, S, t), t))
                    + Cardinality(DueC(ImgN(Image(doc, S, t),
                                            DueN(Image(doc, S, t), t)), t))
                    + Cardinality({ i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                           DueN(Image(doc, S, t), t)),
                                                     DueC(ImgN(Image(doc, S, t),
                                                               DueN(Image(doc, S, t), t)),
                                                          t),
                                                     t) :
                                      ImgC(ImgN(Image(doc, S, t),
                                                DueN(Image(doc, S, t), t)),
                                           DueC(ImgN(Image(doc, S, t),
                                                     DueN(Image(doc, S, t), t)), t),
                                           t)[i].task.state = "acquired"
                                      /\ ImgC(ImgN(Image(doc, S, t),
                                                   DueN(Image(doc, S, t), t)),
                                              DueC(ImgN(Image(doc, S, t),
                                                        DueN(Image(doc, S, t), t)), t),
                                              t)[i].task.leaseTimeoutAt <= t })
                    + Cardinality({ j \in DOMAIN ImgL(ImgC(ImgN(Image(doc, S, t),
                                                               DueN(Image(doc, S, t), t)),
                                                          DueC(ImgN(Image(doc, S, t),
                                                                    DueN(Image(doc, S, t), t)),
                                                               t),
                                                          t),
                                                     { i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                                              DueN(Image(doc, S, t), t)),
                                                                        DueC(ImgN(Image(doc, S, t),
                                                                                  DueN(Image(doc, S, t), t)),
                                                                             t),
                                                                        t) :
                                                         ImgC(ImgN(Image(doc, S, t),
                                                                   DueN(Image(doc, S, t), t)),
                                                              DueC(ImgN(Image(doc, S, t),
                                                                        DueN(Image(doc, S, t), t)), t),
                                                              t)[i].task.state = "acquired"
                                                         /\ ImgC(ImgN(Image(doc, S, t),
                                                                      DueN(Image(doc, S, t), t)),
                                                                 DueC(ImgN(Image(doc, S, t),
                                                                           DueN(Image(doc, S, t), t)), t),
                                                                 t)[i].task.leaseTimeoutAt <= t },
                                                     t) :
                                      ImgL(ImgC(ImgN(Image(doc, S, t),
                                                     DueN(Image(doc, S, t), t)),
                                                DueC(ImgN(Image(doc, S, t),
                                                          DueN(Image(doc, S, t), t)), t),
                                                t),
                                           { i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                                    DueN(Image(doc, S, t), t)),
                                                              DueC(ImgN(Image(doc, S, t),
                                                                        DueN(Image(doc, S, t), t)),
                                                                   t),
                                                              t) :
                                               ImgC(ImgN(Image(doc, S, t),
                                                         DueN(Image(doc, S, t), t)),
                                                    DueC(ImgN(Image(doc, S, t),
                                                              DueN(Image(doc, S, t), t)), t),
                                                    t)[i].task.state = "acquired"
                                               /\ ImgC(ImgN(Image(doc, S, t),
                                                            DueN(Image(doc, S, t), t)),
                                                       DueC(ImgN(Image(doc, S, t),
                                                                 DueN(Image(doc, S, t), t)), t),
                                                       t)[i].task.leaseTimeoutAt <= t },
                                           t)[j].task.state = "pending"
                                      /\ ImgL(ImgC(ImgN(Image(doc, S, t),
                                                        DueN(Image(doc, S, t), t)),
                                                   DueC(ImgN(Image(doc, S, t),
                                                             DueN(Image(doc, S, t), t)), t),
                                                   t),
                                              { i \in DOMAIN ImgC(ImgN(Image(doc, S, t),
                                                                       DueN(Image(doc, S, t), t)),
                                                                 DueC(ImgN(Image(doc, S, t),
                                                                           DueN(Image(doc, S, t), t)),
                                                                      t),
                                                                 t) :
                                                  ImgC(ImgN(Image(doc, S, t),
                                                            DueN(Image(doc, S, t), t)),
                                                       DueC(ImgN(Image(doc, S, t),
                                                                 DueN(Image(doc, S, t), t)), t),
                                                       t)[i].task.state = "acquired"
                                                  /\ ImgC(ImgN(Image(doc, S, t),
                                                               DueN(Image(doc, S, t), t)),
                                                          DueC(ImgN(Image(doc, S, t),
                                                                    DueN(Image(doc, S, t), t)), t),
                                                          t)[i].task.leaseTimeoutAt <= t },
                                              t)[j].task.retryTimeoutAt <= t }))
PROOF
    <1> DEFINE imB == Image(base, S, t)
    <1> DEFINE imD == Image(doc, S, t)
    <1> DEFINE pairs == DueN(imD, t)
    <1> DEFINE docL == ImgN(imD, pairs)
    <1> DEFINE mid == ImgN(imB, pairs)
    <1> DEFINE boxL == BoxN(box, imB, pairs, t)
    <1> DEFINE calls == DueC(docL, t)
    <1> DEFINE cbB == ImgC(mid, calls, t)
    <1> DEFINE cbD == ImgC(docL, calls, t)
    <1> DEFINE exp ==
            { i \in DOMAIN cbD :
                cbD[i].task.state = "acquired"
                /\ cbD[i].task.leaseTimeoutAt <= t }
    <1> DEFINE n3 ==
            Cardinality(S) + Cardinality(pairs) + Cardinality(calls)
    <1> DEFINE ldB == ImgL(cbB, exp, t)
    <1> DEFINE ldD == ImgL(cbD, exp, t)
    <1> DEFINE rset ==
            { j \in DOMAIN ldD :
                ldD[j].task.state = "pending"
                /\ ldD[j].task.retryTimeoutAt <= t }
    <1> DEFINE nL == n3 + Cardinality(exp)
    <1>1. DOMAIN doc \subseteq DOMAIN base /\ DOMAIN doc \subseteq Id
        BY Zenon
    <1>2. S \subseteq DOMAIN doc
        BY Zenon
    <1>3. DOMAIN imD = DOMAIN doc /\ DOMAIN imB = DOMAIN base
        <2>1. S \subseteq DOMAIN base
            BY <1>1, <1>2, Zenon
        <2>2. QED
            BY <1>2, <2>1, ImageDom DEF imD, imB
    <1>4. DOMAIN docL = DOMAIN imD /\ DOMAIN mid = DOMAIN imB
        BY DomImgN DEF docL, mid, imD, imB, pairs
    <1>5. DOMAIN cbD = DOMAIN docL /\ DOMAIN cbB = DOMAIN mid
        BY DomImgC DEF cbD, cbB, docL, mid, calls
    <1>6. DOMAIN cbD \subseteq DOMAIN cbB /\ DOMAIN cbD \subseteq Id
        BY <1>1, <1>3, <1>4, <1>5, Zenon
    <1>7. \A k \in DOMAIN imD : imB[k] = imD[k]
        BY <1>1, <1>2, AgreeImage DEF imB, imD
    <1>8. DOMAIN imD \subseteq DOMAIN imB
        BY <1>1, <1>3, Zenon
    <1>9. \A k \in DOMAIN docL : mid[k] = docL[k]
        BY <1>7, <1>8, AgreeImgN DEF imB, imD, docL, mid, pairs
    <1>10. DOMAIN docL \subseteq DOMAIN mid
        BY <1>1, <1>3, <1>4, Zenon
    <1>11. \A k \in DOMAIN cbD : cbB[k] = cbD[k]
        BY <1>9, <1>10, AgreeImgC DEF mid, docL, cbB, cbD, calls
    <1>12. exp \subseteq DOMAIN cbD
        BY ONLY Zenon DEF exp
    <1>13. \A k \in DOMAIN cbD : P!Project(cbD[k], t) = cbD[k]
        BY FixedPass DEF imD, pairs, docL, calls, cbD
    <1>14. \A k \in DOMAIN cbD :
              cbD[k].task.state = "acquired" =>
                  /\ cbD[k].task.leaseTimeoutAt /= NoTime
                  /\ cbD[k].promise.state = "pending"
        BY <1>2, LeasePass DEF imD, pairs, docL, calls, cbD
    <1>15. \A k \in DOMAIN cbD :
              cbD[k].task.state = "pending" =>
                  /\ cbD[k].task.retryTimeoutAt /= NoTime
                  /\ cbD[k].promise.state = "pending"
        BY <1>2, RetryPass DEF imD, pairs, docL, calls, cbD
    <1>16. ASSUME NEW k \in exp
           PROVE  cbD[k].promise.state = "pending"
        <2>1. k \in DOMAIN cbD /\ cbD[k].task.state = "acquired"
            BY ONLY <1>16, Zenon DEF exp
        <2>2. QED
            BY <1>14, <2>1, Zenon
    <1>17. \A k \in exp : cbD[k].promise.state = "pending"
        BY <1>16
    <1>18. DOMAIN ldD = DOMAIN cbD /\ DOMAIN ldB = DOMAIN cbB
        BY DomImgL DEF ldD, ldB, cbD, cbB, exp
    <1>19. DOMAIN ldD \subseteq DOMAIN ldB /\ DOMAIN ldD \subseteq Id
        BY <1>6, <1>18, Zenon
    <1>20. \A k \in DOMAIN ldD : ldB[k] = ldD[k]
        BY <1>6, <1>11, <1>12, AgreeImgL DEF cbB, cbD, ldB, ldD, exp
    <1>21. \A k \in DOMAIN ldD : P!Project(ldD[k], t) = ldD[k]
        BY <1>12, <1>13, FixedImgL DEF cbD, ldD, exp
    <1>22. \A k \in DOMAIN ldD :
              ldD[k].task.state = "pending" =>
                  /\ ldD[k].task.retryTimeoutAt /= NoTime
                  /\ ldD[k].promise.state = "pending"
        BY <1>12, <1>15, <1>17, RetryImgL DEF cbD, ldD, exp
    <1>23. ReachN(base, box, t, ldB, boxL, nL)
        BY LeaseJoin DEF imB, imD, pairs, docL, mid, boxL, calls, cbB, cbD,
                      exp, n3, ldB, nL
    <1>24. ReachN(ldB, boxL, t, ImgR(ldB, rset, t), BoxAt(boxL, ldB, rset),
                  Cardinality(rset))
        BY <1>19, <1>20, <1>21, <1>22, RetryFrom DEF ldB, ldD, boxL, rset
    <1>25. Cardinality(S) \in Nat
        <2>1. Cardinality(S) \in 0 .. P!MaxSweep
            BY TimeoutChain
        <2>2. P!MaxSweep \in Nat
            BY SweepCap
        <2>3. QED
            BY <2>1, <2>2, Z3
    <1>26. Cardinality(pairs) \in Nat
        <2>1. DOMAIN imD \subseteq Id
            BY <1>1, <1>3, Zenon
        <2>2. IsFiniteSet(pairs)
            BY <2>1, PairFinite DEF pairs, imD
        <2>3. QED
            BY <2>2, FS_CardinalityType
    <1>27. Cardinality(calls) \in Nat
        <2>1. DOMAIN docL \subseteq Id
            BY <1>1, <1>3, <1>4, Zenon
        <2>2. IsFiniteSet(calls)
            BY <2>1, AwFinite DEF calls, docL
        <2>3. QED
            BY <2>2, FS_CardinalityType
    <1>28. n3 \in Nat
        BY <1>25, <1>26, <1>27, Z3 DEF n3
    <1>29. Cardinality(exp) \in Nat
        <2>1. exp \subseteq Id
            BY ONLY <1>6, <1>12, Zenon
        <2>2. IsFiniteSet(exp)
            BY ONLY <2>1, SubCap
        <2>3. QED
            BY ONLY <2>2, FS_CardinalityType
    <1>30. nL \in Nat
        BY ONLY <1>28, <1>29, Z3 DEF nL
    <1>31. Cardinality(rset) \in Nat
        <2>1. rset \subseteq DOMAIN ldD
            BY ONLY Zenon DEF rset
        <2>2. rset \subseteq Id
            BY ONLY <1>19, <2>1, Zenon
        <2>3. IsFiniteSet(rset)
            BY ONLY <2>2, SubCap
        <2>4. QED
            BY ONLY <2>3, FS_CardinalityType
    <1>32. ReachN(base, box, t,
                  ImgR(ldB, rset, t), BoxAt(boxL, ldB, rset),
                  nL + Cardinality(rset))
        BY <1>23, <1>24, <1>30, <1>31, ReachCat DEF ldB, boxL, rset, nL
    <1>33. QED
        BY <1>32 DEF imB, imD, pairs, docL, mid, calls, cbB, cbD, boxL,
                     exp, n3, ldB, ldD, rset, nL

(* The concrete sweep's lease document. Same passes as the outbox. *)
ExpireDoc(doc, t) ==
    SweepExpiresAt(
        SweepCallbacks(
            SweepListeners(SweepTimeoutAt(doc, t).doc, t).doc, t).doc, t).doc

(* Under the shape guards, that document is already projected and its
   pending tasks are due retries. The concrete retry ids are DueR. *)
LEMMA ExpireDue ==
    ASSUME NEW doc, NEW t,
           t /= NoTime,
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address,
           \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  /\ \A k \in DOMAIN ExpireDoc(doc, t) :
                 P!Project(ExpireDoc(doc, t)[k], t) = ExpireDoc(doc, t)[k]
           /\ \A k \in DOMAIN ExpireDoc(doc, t) :
                 ExpireDoc(doc, t)[k].task.state = "pending" =>
                     /\ ExpireDoc(doc, t)[k].task.retryTimeoutAt /= NoTime
                     /\ ExpireDoc(doc, t)[k].promise.state = "pending"
           /\ { i \in DOMAIN ExpireDoc(doc, t) :
                  ExpireDoc(doc, t)[i].task.state = "pending"
                  /\ ExpireDoc(doc, t)[i].task.retryTimeoutAt <= t }
                 = DueR(ExpireDoc(doc, t), t)
PROOF
    <1> DEFINE S ==
            { i \in DOMAIN doc :
                doc[i].promise.state = "pending"
                /\ doc[i].promise.timeoutAt <= t }
    <1> DEFINE im == Image(doc, S, t)
    <1> DEFINE tdoc == SweepTimeoutAt(doc, t).doc
    <1> DEFINE pairs == DueN(im, t)
    <1> DEFINE ln == ImgN(im, pairs)
    <1> DEFINE ldoc == SweepListeners(tdoc, t).doc
    <1> DEFINE calls == DueC(ln, t)
    <1> DEFINE cb == ImgC(ln, calls, t)
    <1> DEFINE cdoc == SweepCallbacks(ldoc, t).doc
    <1> DEFINE exp ==
            { i \in DOMAIN cb :
                cb[i].task.state = "acquired"
                /\ cb[i].task.leaseTimeoutAt <= t }
    <1> DEFINE ld == ImgL(cb, exp, t)
    <1> DEFINE edoc == SweepExpiresAt(cdoc, t).doc
    <1>1. S \subseteq DOMAIN doc
        BY DEF S
    <1>2. S = { i \in DOMAIN doc :
                  /\ doc[i].promise.state = "pending"
                  /\ doc[i].promise.timeoutAt <= t }
        BY DEF S
    <1>3. tdoc = im
        BY <1>2, TimeoutDoc DEF tdoc, im
    <1>4. DOMAIN im = DOMAIN doc
        BY <1>1, ImageDom DEF im
    <1>5. \A k \in DOMAIN doc : P!Project(im[k], t) = im[k]
        BY SliceFixed DEF S, im
    <1>6. \A k \in DOMAIN im : P!Project(im[k], t) = im[k]
        <2> SUFFICES ASSUME NEW k \in DOMAIN im
                     PROVE  P!Project(im[k], t) = im[k]
            OBVIOUS
        <2>1. k \in DOMAIN doc
            BY <1>4
        <2>2. QED
            BY <1>5, <2>1
    <1>7. \A k \in DOMAIN im : im[k].promise.callbacks \subseteq Id
        BY <1>1, CallsOn DEF im
    <1>8. SweepListeners(im, t).doc = ln
        BY ListenAfter DEF S, im, pairs, ln
    <1>9. ldoc = ln
        BY <1>3, <1>8 DEF tdoc, ldoc
    <1>10. SweepCallbacks(ImgN(im, pairs), t).doc
             = ImgC(ImgN(im, pairs), DueC(ImgN(im, pairs), t), t)
        BY <1>6, <1>7, CallAfter DEF im, pairs
    <1>11. cdoc = cb
        BY <1>9, <1>10 DEF ldoc, cdoc, ln, pairs, calls, cb
    <1>12. \A k \in DOMAIN cb : P!Project(cb[k], t) = cb[k]
        BY FixedPass DEF S, im, pairs, ln, calls, cb
    <1>13. \A k \in DOMAIN cb :
              cb[k].task.state = "pending" =>
                  /\ cb[k].task.retryTimeoutAt /= NoTime
                  /\ cb[k].promise.state = "pending"
        BY <1>1, RetryPass DEF im, pairs, ln, calls, cb
    <1>14. \A k \in DOMAIN cb :
              cb[k].task.state = "acquired" =>
                  /\ cb[k].task.leaseTimeoutAt /= NoTime
                  /\ cb[k].promise.state = "pending"
        BY <1>1, LeasePass DEF im, pairs, ln, calls, cb
    <1>15. exp \subseteq DOMAIN cb
        BY DEF exp
    <1>16. ASSUME NEW k \in exp
           PROVE  cb[k].promise.state = "pending"
        <2>1. k \in DOMAIN cb /\ cb[k].task.state = "acquired"
            BY ONLY <1>16, Zenon DEF exp
        <2>2. QED
            BY <1>14, <2>1, Zenon
    <1>17. \A k \in exp : cb[k].promise.state = "pending"
        BY <1>16
    <1>18. SweepExpiresAt(cb, t).doc = ld
        BY LeaseDoc DEF cb, exp, ld
    <1>19. edoc = ld
        BY <1>11, <1>18 DEF cdoc, edoc
    <1>20. \A k \in DOMAIN ld : P!Project(ld[k], t) = ld[k]
        BY <1>12, <1>15, FixedImgL DEF cb, exp, ld
    <1>21. \A k \in DOMAIN ld :
              ld[k].task.state = "pending" =>
                  /\ ld[k].task.retryTimeoutAt /= NoTime
                  /\ ld[k].promise.state = "pending"
        BY <1>13, <1>15, <1>17, RetryImgL DEF cb, exp, ld
    <1>22. { i \in DOMAIN ld :
               ld[i].task.state = "pending"
               /\ ld[i].task.retryTimeoutAt <= t }
            = DueR(ld, t)
        BY <1>20, <1>21, RetryShape
    <1>23. \A k \in DOMAIN edoc : P!Project(edoc[k], t) = edoc[k]
        <2> SUFFICES ASSUME NEW k \in DOMAIN edoc
                     PROVE  P!Project(edoc[k], t) = edoc[k]
            OBVIOUS
        <2>1. k \in DOMAIN ld /\ edoc[k] = ld[k]
            BY <1>19
        <2>2. QED
            BY <1>20, <2>1
    <1>24. \A k \in DOMAIN edoc :
              edoc[k].task.state = "pending" =>
                  /\ edoc[k].task.retryTimeoutAt /= NoTime
                  /\ edoc[k].promise.state = "pending"
        <2> SUFFICES ASSUME NEW k \in DOMAIN edoc
                     PROVE  edoc[k].task.state = "pending" =>
                                /\ edoc[k].task.retryTimeoutAt /= NoTime
                                /\ edoc[k].promise.state = "pending"
            OBVIOUS
        <2>1. k \in DOMAIN ld /\ edoc[k] = ld[k]
            BY <1>19
        <2>2. QED
            BY <1>21, <2>1, Zenon
    <1>25. { i \in DOMAIN edoc :
               edoc[i].task.state = "pending"
               /\ edoc[i].task.retryTimeoutAt <= t }
            = DueR(edoc, t)
        <2>1. { i \in DOMAIN edoc :
                  edoc[i].task.state = "pending"
                  /\ edoc[i].task.retryTimeoutAt <= t }
                = { i \in DOMAIN ld :
                      ld[i].task.state = "pending"
                      /\ ld[i].task.retryTimeoutAt <= t }
            BY <1>19, Zenon
        <2>2. DueR(edoc, t) = DueR(ld, t)
            BY <1>19 DEF DueR
        <2>3. QED
            BY <1>22, <2>1, <2>2
    <1>26. QED
        BY <1>23, <1>24, <1>25 DEF edoc, cdoc, ldoc, tdoc, ExpireDoc

(* The sweep's document is the retry pass of the lease document, and that
   pass is the abstract retry image at DueR. *)
LEMMA SweepRetryImg ==
    ASSUME NEW doc, NEW t,
           t /= NoTime,
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address,
           \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id,
           \A k \in DOMAIN doc :
               doc[k].task.state = "acquired" =>
                   /\ doc[k].task.leaseTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "pending" =>
                   /\ doc[k].task.retryTimeoutAt /= NoTime
                   /\ doc[k].promise.state = "pending",
           \A k \in DOMAIN doc :
               doc[k].task.state = "suspended" =>
                   doc[k].promise.state = "pending"
    PROVE  Sweep(doc, t).doc
              = ImgR(ExpireDoc(doc, t), DueR(ExpireDoc(doc, t), t), t)
PROOF
    <1> DEFINE tmo == SweepTimeoutAt(doc, t)
    <1> DEFINE lis == SweepListeners(tmo.doc, t)
    <1> DEFINE cb == SweepCallbacks(lis.doc, t)
    <1> DEFINE ex == SweepExpiresAt(cb.doc, t)
    <1> DEFINE ry == SweepRetryAt(ex.doc, t)
    <1> DEFINE a1 == SweepTimeoutAt(doc, t)
    <1> DEFINE a2 == Merge(a1, SweepListeners(a1.doc, t))
    <1> DEFINE a3 == Merge(a2, SweepCallbacks(a2.doc, t))
    <1> DEFINE a4 == Merge(a3, SweepExpiresAt(a3.doc, t))
    <1> DEFINE a5 == Merge(a4, SweepRetryAt(a4.doc, t))
    <1> DEFINE edoc == ExpireDoc(doc, t)
    <1> DEFINE due ==
            { i \in DOMAIN edoc :
                edoc[i].task.state = "pending"
                /\ edoc[i].task.retryTimeoutAt <= t }
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
    <1>2. a1 = tmo
        BY DEF a1, tmo
    <1>3. a2.doc = lis.doc
        BY <1>2 DEF a2, lis, Merge
    <1>4. a3.doc = cb.doc
        BY <1>3 DEF a3, cb, Merge
    <1>5. a4.doc = ex.doc
        BY <1>4 DEF a4, ex, Merge
    <1>6. SweepRetryAt(a4.doc, t) = ry
        BY <1>5 DEF ry
    <1>7. a5.doc = ry.doc
        BY <1>6 DEF a5, Merge
    <1>8. Sweep(doc, t).doc = ry.doc
        BY <1>1, <1>7
    <1>9. ex.doc = edoc
        BY DEF ex, cb, lis, tmo, edoc, ExpireDoc
    <1>10. ry.doc = SweepRetryAt(edoc, t).doc
        BY <1>9 DEF ry
    <1>11. due = DueR(edoc, t)
        BY ExpireDue DEF due, edoc
    <1>12. SweepRetryAt(edoc, t).doc = ImgR(edoc, due, t)
        BY RetryDoc DEF due
    <1>13. ImgR(edoc, due, t) = ImgR(edoc, DueR(edoc, t), t)
        BY <1>11 DEF ImgR
    <1>14. QED
        BY <1>8, <1>10, <1>12, <1>13 DEF edoc

(* The lease document is the abstract image of the timeout, listener,
   callback, and lease passes. *)
LEMMA ExpireIs ==
    ASSUME NEW doc, NEW t,
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address,
           \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id
    PROVE  LET S ==
                { i \in DOMAIN doc :
                    doc[i].promise.state = "pending"
                    /\ doc[i].promise.timeoutAt <= t }
               im == Image(doc, S, t)
               ln == ImgN(im, DueN(im, t))
               cb == ImgC(ln, DueC(ln, t), t)
               exp ==
                { i \in DOMAIN cb :
                    cb[i].task.state = "acquired"
                    /\ cb[i].task.leaseTimeoutAt <= t }
           IN  ExpireDoc(doc, t) = ImgL(cb, exp, t)
PROOF
    <1> DEFINE S ==
            { i \in DOMAIN doc :
                doc[i].promise.state = "pending"
                /\ doc[i].promise.timeoutAt <= t }
    <1> DEFINE im == Image(doc, S, t)
    <1> DEFINE tdoc == SweepTimeoutAt(doc, t).doc
    <1> DEFINE pairs == DueN(im, t)
    <1> DEFINE ln == ImgN(im, pairs)
    <1> DEFINE ldoc == SweepListeners(tdoc, t).doc
    <1> DEFINE calls == DueC(ln, t)
    <1> DEFINE cb == ImgC(ln, calls, t)
    <1> DEFINE cdoc == SweepCallbacks(ldoc, t).doc
    <1> DEFINE exp ==
            { i \in DOMAIN cb :
                cb[i].task.state = "acquired"
                /\ cb[i].task.leaseTimeoutAt <= t }
    <1> DEFINE ld == ImgL(cb, exp, t)
    <1> DEFINE edoc == SweepExpiresAt(cdoc, t).doc
    <1>1. S \subseteq DOMAIN doc
        BY DEF S
    <1>2. S = { i \in DOMAIN doc :
                  /\ doc[i].promise.state = "pending"
                  /\ doc[i].promise.timeoutAt <= t }
        BY DEF S
    <1>3. tdoc = im
        BY <1>2, TimeoutDoc DEF tdoc, im
    <1>4. DOMAIN im = DOMAIN doc
        BY <1>1, ImageDom DEF im
    <1>5. \A k \in DOMAIN doc : P!Project(im[k], t) = im[k]
        BY SliceFixed DEF S, im
    <1>6. \A k \in DOMAIN im : P!Project(im[k], t) = im[k]
        <2> SUFFICES ASSUME NEW k \in DOMAIN im
                     PROVE  P!Project(im[k], t) = im[k]
            OBVIOUS
        <2>1. k \in DOMAIN doc
            BY <1>4
        <2>2. QED
            BY <1>5, <2>1
    <1>7. \A k \in DOMAIN im : im[k].promise.callbacks \subseteq Id
        BY <1>1, CallsOn DEF im
    <1>8. SweepListeners(im, t).doc = ln
        BY ListenAfter DEF S, im, pairs, ln
    <1>9. ldoc = ln
        BY <1>3, <1>8 DEF tdoc, ldoc
    <1>10. SweepCallbacks(ImgN(im, pairs), t).doc
             = ImgC(ImgN(im, pairs), DueC(ImgN(im, pairs), t), t)
        BY <1>6, <1>7, CallAfter DEF im, pairs
    <1>11. cdoc = cb
        BY <1>9, <1>10 DEF ldoc, cdoc, ln, pairs, calls, cb
    <1>12. SweepExpiresAt(cb, t).doc = ld
        BY LeaseDoc DEF cb, exp, ld
    <1>13. edoc = ld
        BY <1>11, <1>12 DEF cdoc, edoc
    <1>14. ExpireDoc(doc, t) = edoc
        BY DEF ExpireDoc, edoc, cdoc, ldoc, tdoc
    <1>15. QED
        BY <1>13, <1>14 DEF ld, cb, exp, ln, im, pairs, calls, S

(* A retry body depends only on the object it rewrites. *)
LEMMA SameRetry ==
    ASSUME NEW a, NEW b, NEW t, a = b
    PROVE  RetryBody(a, t) = RetryBody(b, t)
PROOF
    BY Zenon

(* Planting one origin's retry image is the retry image of the whole store.
   Ids outside that origin are not in the retry set, so they stay. *)
LEMMA PlantR ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW T,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           T \subseteq DOMAIN doc,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  Plant(base, o, ImgR(doc, T, t)) = ImgR(base, T, t)
PROOF
    <1>1. CASE T = {}
        <2>1. ImgR(doc, T, t) = doc /\ ImgR(base, T, t) = base
            BY <1>1 DEF ImgR
        <2>2. Plant(base, o, doc) = base
            BY PlantId
        <2>3. QED
            BY <2>1, <2>2
    <1>2. CASE T # {}
        <2> DEFINE body ==
                [ i \in DOMAIN doc |->
                    IF i \in T THEN RetryBody(doc[i], t) ELSE doc[i] ]
        <2> DEFINE full ==
                [ i \in DOMAIN base |->
                    IF i \in T THEN RetryBody(base[i], t) ELSE base[i] ]
        <2>1. ImgR(doc, T, t) = body
            BY <1>2 DEF ImgR, body
        <2>2. ImgR(base, T, t) = full
            BY <1>2 DEF ImgR, full
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
            <3>1. full[k] = (IF k \in T THEN RetryBody(base[k], t) ELSE base[k])
                BY Zenon DEF full
            <3>2. CASE k \in DOMAIN doc
                <4>1. k \in DOMAIN body
                    BY <2>3, <3>2
                <4>2. body[k] = (IF k \in T THEN RetryBody(doc[k], t) ELSE doc[k])
                    BY <2>3, <3>2, Zenon DEF body
                <4>3. base[k] = doc[k]
                    BY <3>2, Zenon
                <4>4. RetryBody(base[k], t) = RetryBody(doc[k], t)
                    BY <4>3, SameRetry
                <4>5. QED
                    BY <3>1, <4>1, <4>2, <4>3, <4>4, Z3
            <3>3. CASE k \notin DOMAIN doc
                <4>1. k \notin DOMAIN body
                    BY <2>3, <3>3
                <4>2. k \notin T
                    BY <3>3, Zenon
                <4>3. full[k] = base[k]
                    BY <3>1, <4>2, Z3
                <4>4. QED
                    BY <4>1, <4>3
            <3>4. QED
                BY <3>2, <3>3
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

(* Every due listener pair names an id of the document. *)
LEMMA DueNIn ==
    ASSUME NEW o, NEW t
    PROVE  DueN(o, t) \subseteq [id : DOMAIN o, address : Address]
PROOF
    <1>1. ASSUME NEW p \in DueN(o, t)
          PROVE  p \in [id : DOMAIN o, address : Address]
        <2> DEFINE ids ==
                { q \in DOMAIN o :
                    P!Project(o[q], t).promise.state /= "pending" }
        <2>1. p \in [id : ids, address : Address]
            BY <1>1, InDue DEF ids
        <2>2. QED
            BY <2>1, Z3 DEF ids
    <1>2. QED
        BY <1>1

(* An Unblock reads only the projected state at its id. *)
LEMMA SameUnblock ==
    ASSUME NEW base, NEW doc, NEW i, NEW addr, NEW t,
           i \in DOMAIN base, i \in DOMAIN doc,
           base[i] = doc[i]
    PROVE  UnblockMsg(base, i, addr, t) = UnblockMsg(doc, i, addr, t)
PROOF
    <1>1. P!Project(base[i], t) = P!Project(doc[i], t)
        BY Zenon
    <1>2. P!Project(base[i], t).promise.state
            = P!Project(doc[i], t).promise.state
        BY <1>1, Zenon
    <1>3. QED
        BY <1>2, Isa DEF UnblockMsg

(* Listener messages agree when the two stores agree on every pair id. *)
LEMMA SameMsgN ==
    ASSUME NEW base, NEW doc, NEW P, NEW t,
           P \subseteq [id : DOMAIN doc, address : Address],
           DOMAIN doc \subseteq DOMAIN base,
           \A k \in DOMAIN doc : base[k] = doc[k]
    PROVE  MsgN(base, P, t) = MsgN(doc, P, t)
PROOF
    <1>1. \A p \in P :
             UnblockMsg(base, p.id, p.address, t)
               = UnblockMsg(doc, p.id, p.address, t)
        <2> SUFFICES ASSUME NEW p \in P
                     PROVE  UnblockMsg(base, p.id, p.address, t)
                              = UnblockMsg(doc, p.id, p.address, t)
            OBVIOUS
        <2>1. p.id \in DOMAIN doc /\ p.address \in Address
            BY Z3
        <2>2. p.id \in DOMAIN base /\ base[p.id] = doc[p.id]
            BY <2>1, Zenon
        <2>3. QED
            BY <2>1, <2>2, SameUnblock
    <1>2. \A m : m \in MsgN(base, P, t) <=> m \in MsgN(doc, P, t)
        BY <1>1, Zenon DEF MsgN
    <1>3. QED
        BY <1>2, IsaWithSetExtensionality

LEMMA SameBoxN ==
    ASSUME NEW b, NEW base, NEW doc, NEW P, NEW t,
           P \subseteq [id : DOMAIN doc, address : Address],
           DOMAIN doc \subseteq DOMAIN base,
           \A k \in DOMAIN doc : base[k] = doc[k]
    PROVE  BoxN(b, base, P, t) = BoxN(b, doc, P, t)
PROOF
    <1>1. MsgN(base, P, t) = MsgN(doc, P, t)
        BY SameMsgN
    <1>2. QED
        BY <1>1 DEF BoxN

(* An Execute reads only the target and the version at its id. *)
LEMMA SameExec ==
    ASSUME NEW base, NEW doc, NEW i,
           i \in DOMAIN base, i \in DOMAIN doc,
           base[i] = doc[i]
    PROVE  RetryMsg(base, i) = RetryMsg(doc, i)
PROOF
    BY Isa DEF RetryMsg

LEMMA SameMsgs ==
    ASSUME NEW base, NEW doc, NEW T,
           T \subseteq DOMAIN doc,
           DOMAIN doc \subseteq DOMAIN base,
           \A k \in DOMAIN doc : base[k] = doc[k]
    PROVE  Msgs(base, T) = Msgs(doc, T)
PROOF
    <1>1. \A i \in T : RetryMsg(base, i) = RetryMsg(doc, i)
        <2> SUFFICES ASSUME NEW i \in T
                     PROVE  RetryMsg(base, i) = RetryMsg(doc, i)
            OBVIOUS
        <2>1. i \in DOMAIN doc
            BY Zenon
        <2>2. i \in DOMAIN base /\ base[i] = doc[i]
            BY <2>1, Zenon
        <2>3. QED
            BY <2>1, <2>2, SameExec
    <1>2. \A m : m \in Msgs(base, T) <=> m \in Msgs(doc, T)
        BY <1>1, Zenon DEF Msgs
    <1>3. QED
        BY <1>2, IsaWithSetExtensionality

LEMMA SameBoxAt ==
    ASSUME NEW b, NEW base, NEW doc, NEW T,
           T \subseteq DOMAIN doc,
           DOMAIN doc \subseteq DOMAIN base,
           \A k \in DOMAIN doc : base[k] = doc[k]
    PROVE  BoxAt(b, base, T) = BoxAt(b, doc, T)
PROOF
    <1>1. Msgs(base, T) = Msgs(doc, T)
        BY SameMsgs
    <1>2. QED
        BY <1>1 DEF BoxAt

(* The callback image of an eta store is eta. *)
LEMMA EtaImgC ==
    ASSUME NEW base, NEW S, NEW t,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  ImgC(base, S, t)
              = [ i \in DOMAIN ImgC(base, S, t) |-> ImgC(base, S, t)[i] ]
PROOF
    <1>1. CASE S = {}
        <2>1. ImgC(base, S, t) = base
            BY <1>1 DEF ImgC
        <2>2. DOMAIN ImgC(base, S, t) = DOMAIN base
            BY <2>1
        <2>3. QED
            BY <2>1, <2>2, Zenon
    <1>2. CASE S # {}
        <2> DEFINE f == [ j \in DOMAIN base |-> BodyC(base, S, j, t) ]
        <2>1. ImgC(base, S, t) = f
            BY <1>2 DEF ImgC, f
        <2>2. DOMAIN f = DOMAIN base
            BY DomCtor DEF f
        <2>3. \A k \in DOMAIN base : f[k] = BodyC(base, S, k, t)
            BY Zenon DEF f
        <2>4. f = [ i \in DOMAIN f |-> f[i] ]
            BY <2>2, <2>3, ExtCtor DEF f
        <2>5. QED
            BY <2>1, <2>4
    <1>3. QED
        BY <1>1, <1>2

(* The lease image of an eta store is eta. *)
LEMMA EtaImgL ==
    ASSUME NEW base, NEW T, NEW t,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  ImgL(base, T, t)
              = [ i \in DOMAIN ImgL(base, T, t) |-> ImgL(base, T, t)[i] ]
PROOF
    <1>1. CASE T = {}
        <2>1. ImgL(base, T, t) = base
            BY <1>1 DEF ImgL
        <2>2. DOMAIN ImgL(base, T, t) = DOMAIN base
            BY <2>1
        <2>3. QED
            BY <2>1, <2>2, Zenon
    <1>2. CASE T # {}
        <2> DEFINE f ==
                [ i \in DOMAIN base |->
                    IF i \in T THEN LeaseBody(base[i], t) ELSE base[i] ]
        <2>1. ImgL(base, T, t) = f
            BY <1>2 DEF ImgL, f
        <2>2. DOMAIN f = DOMAIN base
            BY DomCtor DEF f
        <2>3. \A k \in DOMAIN base :
                f[k] = (IF k \in T THEN LeaseBody(base[k], t) ELSE base[k])
            BY Zenon DEF f
        <2>4. f = [ i \in DOMAIN f |-> f[i] ]
            BY <2>2, <2>3, ExtCtor DEF f
        <2>5. QED
            BY <2>1, <2>4
    <1>3. QED
        BY <1>1, <1>2

(* The retry image of an eta store is eta. *)
LEMMA EtaImgR ==
    ASSUME NEW base, NEW T, NEW t,
           base = [ i \in DOMAIN base |-> base[i] ]
    PROVE  ImgR(base, T, t)
              = [ i \in DOMAIN ImgR(base, T, t) |-> ImgR(base, T, t)[i] ]
PROOF
    <1>1. CASE T = {}
        <2>1. ImgR(base, T, t) = base
            BY <1>1 DEF ImgR
        <2>2. DOMAIN ImgR(base, T, t) = DOMAIN base
            BY <2>1
        <2>3. QED
            BY <2>1, <2>2, Zenon
    <1>2. CASE T # {}
        <2> DEFINE f ==
                [ i \in DOMAIN base |->
                    IF i \in T THEN RetryBody(base[i], t) ELSE base[i] ]
        <2>1. ImgR(base, T, t) = f
            BY <1>2 DEF ImgR, f
        <2>2. DOMAIN f = DOMAIN base
            BY DomCtor DEF f
        <2>3. \A k \in DOMAIN base :
                f[k] = (IF k \in T THEN RetryBody(base[k], t) ELSE base[k])
            BY Zenon DEF f
        <2>4. f = [ i \in DOMAIN f |-> f[i] ]
            BY <2>2, <2>3, ExtCtor DEF f
        <2>5. QED
            BY <2>1, <2>4
    <1>3. QED
        BY <1>1, <1>2

(* Five due sets, one per sweep kind, still fit in MaxSweep.
   Timeouts, leases, and retries are ids. Listeners add an address.
   Callbacks add another id. *)
LEMMA SweepBudget ==
    ASSUME NEW a, NEW b, NEW c, NEW d, NEW e,
           a \subseteq Id,
           d \subseteq Id,
           e \subseteq Id,
           b \subseteq [id : Id, address : Address],
           c \subseteq [id : Id, awaiter : Id]
    PROVE  Cardinality(a) + Cardinality(b) + Cardinality(c)
              + Cardinality(d) + Cardinality(e) \in 0 .. P!MaxSweep
PROOF
    <1> DEFINE OpA(p) == [id |-> p[1], address |-> p[2]]
    <1> DEFINE ImgA == { OpA(p) : p \in Id \X Address }
    <1> DEFINE OpI(p) == [id |-> p[1], awaiter |-> p[2]]
    <1> DEFINE ImgI == { OpI(p) : p \in Id \X Id }
    <1>1. IsFiniteSet(Id) /\ IsFiniteSet(Address)
        BY FiniteOrigin, FiniteRest, FiniteAddress, IdFinite
    <1>2. Cardinality(Id) \in Nat /\ Cardinality(Address) \in Nat
        BY <1>1, FS_CardinalityType
    <1>3. P!MaxSweep
            = Cardinality(Id)
              * (Cardinality(Id) + Cardinality(Address) + 3)
        BY SameId, SameCard DEF P!MaxSweep
    <1>4. P!MaxSweep \in Nat
        BY SweepCap
    <1>5. /\ IsFiniteSet(Id \X Address)
          /\ Cardinality(Id \X Address)
               = Cardinality(Id) * Cardinality(Address)
        BY <1>1, FS_Product
    <1>6. /\ IsFiniteSet(Id \X Id)
          /\ Cardinality(Id \X Id) = Cardinality(Id) * Cardinality(Id)
        BY <1>1, FS_Product
    <1>7. LET T == { OpA(x) : x \in Id \X Address }
          IN  /\ IsFiniteSet(T)
              /\ Cardinality(T) <= Cardinality(Id \X Address)
        <2> DEFINE f == [x \in Id \X Address |-> OpA(x)]
        <2> DEFINE img == { OpA(x) : x \in Id \X Address }
        <2>1. IsFiniteSet(Id \X Address)
            BY <1>5, Zenon
        <2>2. f \in Surjection(Id \X Address, img)
            BY DEF Surjection, f, img
        <2>3. IsFiniteSet(img)
            BY <2>1, <2>2, FS_Surjection, Zenon
        <2>4. Cardinality(img) <= Cardinality(Id \X Address)
            BY <2>1, <2>2, FS_Surjection, Zenon
        <2>5. QED
            BY <2>3, <2>4 DEF img
    <1>8. /\ IsFiniteSet(ImgA)
          /\ Cardinality(ImgA) <= Cardinality(Id \X Address)
        BY <1>7 DEF ImgA
    <1>9. LET T == { OpI(x) : x \in Id \X Id }
          IN  /\ IsFiniteSet(T)
              /\ Cardinality(T) <= Cardinality(Id \X Id)
        <2> DEFINE f == [x \in Id \X Id |-> OpI(x)]
        <2> DEFINE img == { OpI(x) : x \in Id \X Id }
        <2>1. IsFiniteSet(Id \X Id)
            BY <1>6, Zenon
        <2>2. f \in Surjection(Id \X Id, img)
            BY DEF Surjection, f, img
        <2>3. IsFiniteSet(img)
            BY <2>1, <2>2, FS_Surjection, Zenon
        <2>4. Cardinality(img) <= Cardinality(Id \X Id)
            BY <2>1, <2>2, FS_Surjection, Zenon
        <2>5. QED
            BY <2>3, <2>4 DEF img
    <1>10. /\ IsFiniteSet(ImgI)
           /\ Cardinality(ImgI) <= Cardinality(Id \X Id)
        BY <1>9 DEF ImgI
    <1>11. [id : Id, address : Address] \subseteq ImgA
        <2> SUFFICES ASSUME NEW x \in [id : Id, address : Address]
                     PROVE  x \in ImgA
            OBVIOUS
        <2>1. x.id \in Id /\ x.address \in Address
            BY Z3
        <2> DEFINE p == <<x.id, x.address>>
        <2>2. p \in Id \X Address
            BY <2>1, PairIn DEF p
        <2>3. x = [id |-> x.id, address |-> x.address]
            BY RecPair
        <2>4. x = OpA(p)
            BY <2>3 DEF OpA, p
        <2>5. QED
            BY <2>2, <2>4 DEF ImgA
    <1>12. [id : Id, awaiter : Id] \subseteq ImgI
        <2> SUFFICES ASSUME NEW x \in [id : Id, awaiter : Id]
                     PROVE  x \in ImgI
            OBVIOUS
        <2>1. x.id \in Id /\ x.awaiter \in Id
            BY Z3
        <2> DEFINE p == <<x.id, x.awaiter>>
        <2>2. p \in Id \X Id
            BY <2>1, PairIn DEF p
        <2>3. x = [id |-> x.id, awaiter |-> x.awaiter]
            BY RecAw
        <2>4. x = OpI(p)
            BY <2>3 DEF OpI, p
        <2>5. QED
            BY <2>2, <2>4 DEF ImgI
    <1>13. b \subseteq ImgA /\ c \subseteq ImgI
        BY <1>11, <1>12, Zenon
    <1>14. /\ IsFiniteSet(a) /\ Cardinality(a) <= Cardinality(Id)
           /\ IsFiniteSet(d) /\ Cardinality(d) <= Cardinality(Id)
           /\ IsFiniteSet(e) /\ Cardinality(e) <= Cardinality(Id)
        BY <1>1, FS_Subset
    <1>15. /\ IsFiniteSet(b) /\ Cardinality(b) <= Cardinality(ImgA)
           /\ IsFiniteSet(c) /\ Cardinality(c) <= Cardinality(ImgI)
        BY <1>8, <1>10, <1>13, FS_Subset
    <1>16. /\ Cardinality(a) \in Nat
           /\ Cardinality(b) \in Nat
           /\ Cardinality(c) \in Nat
           /\ Cardinality(d) \in Nat
           /\ Cardinality(e) \in Nat
        BY <1>14, <1>15, FS_CardinalityType
    <1>17. Cardinality(b) <= Cardinality(Id) * Cardinality(Address)
        <2>1. Cardinality(b) <= Cardinality(ImgA)
            BY <1>15, Zenon
        <2>2. Cardinality(ImgA) <= Cardinality(Id \X Address)
            BY <1>8, Zenon
        <2>3. Cardinality(Id \X Address)
                = Cardinality(Id) * Cardinality(Address)
            BY <1>5, Zenon
        <2>4. Cardinality(b) \in Nat
            BY <1>16, Zenon
        <2>5. Cardinality(ImgA) \in Nat
            BY <1>8, FS_CardinalityType, Zenon
        <2>6. Cardinality(Id \X Address) \in Nat
            BY <1>5, FS_CardinalityType, Zenon
        <2>7. Cardinality(b) <= Cardinality(Id \X Address)
            BY <2>1, <2>2, <2>4, <2>5, <2>6, Z3
        <2>8. QED
            BY <2>3, <2>7, Z3
    <1>18. Cardinality(c) <= Cardinality(Id) * Cardinality(Id)
        <2>1. Cardinality(c) <= Cardinality(ImgI)
            BY <1>15, Zenon
        <2>2. Cardinality(ImgI) <= Cardinality(Id \X Id)
            BY <1>10, Zenon
        <2>3. Cardinality(Id \X Id) = Cardinality(Id) * Cardinality(Id)
            BY <1>6, Zenon
        <2>4. Cardinality(c) \in Nat
            BY <1>16, Zenon
        <2>5. Cardinality(ImgI) \in Nat
            BY <1>10, FS_CardinalityType, Zenon
        <2>6. Cardinality(Id \X Id) \in Nat
            BY <1>6, FS_CardinalityType, Zenon
        <2>7. Cardinality(c) <= Cardinality(Id \X Id)
            BY <2>1, <2>2, <2>4, <2>5, <2>6, Z3
        <2>8. QED
            BY <2>3, <2>7, Z3
    <1>19. Cardinality(a) + Cardinality(b) + Cardinality(c)
             + Cardinality(d) + Cardinality(e) <= P!MaxSweep
        BY <1>2, <1>3, <1>14, <1>16, <1>17, <1>18, Z3
    <1>20. Cardinality(a) + Cardinality(b) + Cardinality(c)
             + Cardinality(d) + Cardinality(e) \in Nat
        BY <1>16, Z3
    <1>21. QED
        BY <1>4, <1>19, <1>20, Z3

(* Two stores that agree off one origin plant the same document. *)
LEMMA SamePlant ==
    ASSUME NEW a, NEW b, NEW o, NEW body,
           DOMAIN a = DOMAIN b,
           DOMAIN body = { i \in DOMAIN a : i.origin = o },
           \A i \in DOMAIN a : i.origin /= o => a[i] = b[i]
    PROVE  Plant(a, o, body) = Plant(b, o, body)
PROOF
    <1> DEFINE keptA == { j \in DOMAIN a : j.origin /= o }
    <1> DEFINE keptB == { j \in DOMAIN b : j.origin /= o }
    <1> DEFINE domA == keptA \cup DOMAIN body
    <1> DEFINE domB == keptB \cup DOMAIN body
    <1>1. keptA = keptB
        BY Zenon DEF keptA, keptB
    <1>2. domA = domB
        BY <1>1 DEF domA, domB
    <1>3. \A i \in domA :
            (IF i \in DOMAIN body THEN body[i] ELSE a[i])
              = (IF i \in DOMAIN body THEN body[i] ELSE b[i])
        <2> SUFFICES ASSUME NEW k \in domA
                     PROVE  (IF k \in DOMAIN body THEN body[k] ELSE a[k])
                              = (IF k \in DOMAIN body THEN body[k] ELSE b[k])
            OBVIOUS
        <2>1. CASE k \in DOMAIN body
            BY <2>1
        <2>2. CASE k \notin DOMAIN body
            <3>1. k \in keptA
                BY <2>2 DEF domA
            <3>2. k.origin /= o /\ k \in DOMAIN a
                BY <3>1 DEF keptA
            <3>3. a[k] = b[k]
                BY <3>2
            <3>4. QED
                BY <2>2, <3>3
        <2>3. QED
            BY <2>1, <2>2
    <1>4. Plant(a, o, body)
            = [ i \in domA |-> IF i \in DOMAIN body THEN body[i] ELSE a[i] ]
        BY DEF Plant, keptA, domA
    <1>5. Plant(b, o, body)
            = [ i \in domB |-> IF i \in DOMAIN body THEN body[i] ELSE b[i] ]
        BY DEF Plant, keptB, domB
    <1>6. [ i \in domA |-> IF i \in DOMAIN body THEN body[i] ELSE a[i] ]
            = [ i \in domB |-> IF i \in DOMAIN body THEN body[i] ELSE b[i] ]
        BY <1>2, <1>3, ExtCtor
    <1>7. QED
        BY <1>4, <1>5, <1>6

(* An id the timeout pass does not touch keeps its value. *)
LEMMA StayImage ==
    ASSUME NEW base, NEW T, NEW t, NEW k,
           k \in DOMAIN base, T \subseteq DOMAIN base, k \notin T
    PROVE  Image(base, T, t)[k] = base[k]
PROOF
    <1>1. Image(base, T, t)[k]
            = IF k \in T THEN P!Project(base[k], t) ELSE base[k]
        BY ImageVal
    <1>2. QED
        BY <1>1, Z3

(* An id named by no listener pair keeps its value. *)
LEMMA StayN ==
    ASSUME NEW store, NEW P, NEW j, NEW non,
           j \in DOMAIN store,
           j \notin non,
           P \subseteq [id : non, address : Address]
    PROVE  ImgN(store, P)[j] = store[j]
PROOF
    <1>1. CASE P = {}
        BY <1>1 DEF ImgN
    <1>2. CASE P # {}
        <2> DEFINE f == [k \in DOMAIN store |-> BodyN(store, P, k)]
        <2>1. BodyN(store, P, j) = store[j]
            BY IdleBody
        <2>2. ImgN(store, P) = f
            BY <1>2 DEF ImgN, f
        <2>3. f[j] = BodyN(store, P, j)
            BY Zenon DEF f
        <2>4. QED
            BY <2>1, <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2

(* A callback set that never mentions an id leaves that object alone. *)
LEMMA IdleC ==
    ASSUME NEW o, NEW S, NEW j, NEW t,
           \A y \in S : y.id /= j,
           \A y \in S : y.awaiter /= j
    PROVE  BodyC(o, S, j, t) = o[j]
PROOF
    <1> DEFINE drop == Drp(j, S)
    <1> DEFINE src == Src(j, S)
    <1>1. src = {}
        BY SrcOut DEF src
    <1>2. drop = {}
        <2>1. drop = { p.awaiter : p \in { y \in S : y.id = j } }
            BY DEF drop, Drp
        <2>2. { y \in S : y.id = j } = {}
            BY Zenon
        <2>3. { p.awaiter : p \in {} } = {}
            BY Zenon
        <2>4. QED
            BY <2>1, <2>2, <2>3, Zenon
    <1>3. Cleared(o, S, j) = o[j]
        BY <1>2 DEF Cleared, drop
    <1>4. Woken(o[j], src, t) = o[j]
        BY <1>1 DEF Woken, src
    <1>5. BodyC(o, S, j, t) = Woken(Cleared(o, S, j), src, t)
        BY DEF BodyC, src
    <1>6. QED
        BY <1>3, <1>4, <1>5

LEMMA StayC ==
    ASSUME NEW store, NEW S, NEW j, NEW t,
           j \in DOMAIN store,
           \A y \in S : y.id /= j,
           \A y \in S : y.awaiter /= j
    PROVE  ImgC(store, S, t)[j] = store[j]
PROOF
    <1>1. CASE S = {}
        BY <1>1 DEF ImgC
    <1>2. CASE S # {}
        <2> DEFINE f == [k \in DOMAIN store |-> BodyC(store, S, k, t)]
        <2>1. BodyC(store, S, j, t) = store[j]
            BY IdleC
        <2>2. ImgC(store, S, t) = f
            BY <1>2 DEF ImgC, f
        <2>3. f[j] = BodyC(store, S, j, t)
            BY Zenon DEF f
        <2>4. QED
            BY <2>1, <2>2, <2>3
    <1>3. QED
        BY <1>1, <1>2

(* An id of another origin is not touched by this origin's lease image.
   The timeout set, the listener pairs, the callbacks, and the leases
   all name ids of this origin. *)
LEMMA OffLease ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW k,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           k \in DOMAIN base,
           k.origin /= o,
           \A y \in [id : DOMAIN doc, awaiter : Id] :
               y.awaiter \in DOMAIN base => y.awaiter \in DOMAIN doc
    PROVE  LET S ==
                { i \in DOMAIN doc :
                    doc[i].promise.state = "pending"
                    /\ doc[i].promise.timeoutAt <= t }
                imB == Image(base, S, t)
                imD == Image(doc, S, t)
                pairs == DueN(imD, t)
                mid == ImgN(imB, pairs)
                docL == ImgN(imD, pairs)
                calls == DueC(docL, t)
                cbB == ImgC(mid, calls, t)
                cbD == ImgC(docL, calls, t)
                exp ==
                    { i \in DOMAIN cbD :
                        cbD[i].task.state = "acquired"
                        /\ cbD[i].task.leaseTimeoutAt <= t }
            IN  ImgL(cbB, exp, t)[k] = base[k]
PROOF
    <1> DEFINE S ==
            { i \in DOMAIN doc :
                doc[i].promise.state = "pending"
                /\ doc[i].promise.timeoutAt <= t }
    <1> DEFINE imB == Image(base, S, t)
    <1> DEFINE imD == Image(doc, S, t)
    <1> DEFINE pairs == DueN(imD, t)
    <1> DEFINE mid == ImgN(imB, pairs)
    <1> DEFINE docL == ImgN(imD, pairs)
    <1> DEFINE calls == DueC(docL, t)
    <1> DEFINE cbB == ImgC(mid, calls, t)
    <1> DEFINE cbD == ImgC(docL, calls, t)
    <1> DEFINE exp ==
            { i \in DOMAIN cbD :
                cbD[i].task.state = "acquired"
                /\ cbD[i].task.leaseTimeoutAt <= t }
    <1>1. k \notin DOMAIN doc
        BY Zenon
    <1>2. S \subseteq DOMAIN doc /\ S \subseteq DOMAIN base
        BY <1>1 DEF S
    <1>3. k \notin S
        BY <1>1, <1>2, Zenon
    <1>4. imB[k] = base[k]
        BY <1>2, <1>3, StayImage DEF imB
    <1>5. DOMAIN imD = DOMAIN doc /\ DOMAIN imB = DOMAIN base
        BY <1>2, ImageDom DEF imD, imB
    <1>6. pairs \subseteq [id : DOMAIN imD, address : Address]
        BY DueNIn DEF pairs
    <1>7. pairs \subseteq [id : DOMAIN doc, address : Address]
        BY <1>5, <1>6, Zenon
    <1>8. k \in DOMAIN imB
        BY <1>5, Zenon
    <1>9. mid[k] = imB[k]
        BY <1>1, <1>7, <1>8, StayN DEF mid, pairs
    <1>10. mid[k] = base[k]
        BY <1>4, <1>9
    <1>11. DOMAIN docL = DOMAIN imD /\ DOMAIN mid = DOMAIN imB
        BY DomImgN DEF docL, mid, imD, imB, pairs
    <1>12. calls \subseteq [id : DOMAIN docL, awaiter : Id]
        BY AwSub DEF calls
    <1>13. calls \subseteq [id : DOMAIN doc, awaiter : Id]
        BY <1>5, <1>11, <1>12, Zenon
    <1>14. \A y \in calls : y.id /= k /\ y.awaiter /= k
        <2> SUFFICES ASSUME NEW y \in calls
                     PROVE  y.id /= k /\ y.awaiter /= k
            OBVIOUS
        <2>1. y \in [id : DOMAIN doc, awaiter : Id]
            BY <1>13, Zenon
        <2>2. y.id \in DOMAIN doc /\ y.awaiter \in Id
            BY <2>1, Z3
        <2>3. y.id /= k
            BY <1>1, <2>2, Zenon
        <2>4. y.awaiter \in DOMAIN base => y.awaiter \in DOMAIN doc
            BY <2>1, Zenon
        <2>5. y.awaiter /= k
            BY <1>1, <2>2, <2>4, Zenon
        <2>6. QED
            BY <2>3, <2>5
    <1>15. k \in DOMAIN mid
        BY <1>8, <1>11, Zenon
    <1>16. cbB[k] = mid[k]
        BY <1>14, <1>15, StayC DEF cbB, calls
    <1>17. DOMAIN cbD = DOMAIN docL /\ DOMAIN cbB = DOMAIN mid
        BY DomImgC DEF cbD, cbB, docL, mid, calls
    <1>18. exp \subseteq DOMAIN cbD
        BY DEF exp
    <1>19. k \notin exp /\ exp \subseteq DOMAIN cbB /\ k \in DOMAIN cbB
        BY <1>1, <1>5, <1>11, <1>15, <1>17, <1>18, Zenon
    <1>20. ImgL(cbB, exp, t)[k] = cbB[k]
        BY <1>19, LeaseAt DEF cbB, exp
    <1>21. QED
        BY <1>10, <1>16, <1>20 DEF S, imB, imD, pairs, mid, docL,
                                calls, cbB, cbD, exp

===============================================================================
