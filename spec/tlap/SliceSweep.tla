----------------------------- MODULE SliceSweep -----------------------------
(* The slice recorded for a placed document is the store a sweep step
   starts from. Its image is already in the abstract closure. *)
EXTENDS SweepSent

LEMMA AppAt ==
    ASSUME NEW S, NEW e(_), NEW k \in S
    PROVE  [x \in S |-> e(x)][k] = e(k)
PROOF
    BY Z3, Isa

LEMMA ObjEta ==
    ASSUME NEW base,
           base = Objects
    PROVE  base = [ i \in DOMAIN base |-> base[i] ]
PROOF
    <1> DEFINE U == UNION { DOMAIN docs[p] : p \in Origin }
    <1>1. DOMAIN Objects = U
        BY DomCtor, Isa DEF Objects, U
    <1>2. ASSUME NEW i \in U
          PROVE  Objects[i] = docs[i.origin][i]
        BY <1>1, <1>2, AppAt, Isa DEF Objects, U
    <1>3. Objects = [ i \in U |-> docs[i.origin][i] ]
        BY Z3 DEF Objects, U
    <1>4. [ i \in U |-> docs[i.origin][i] ]
            = [ i \in DOMAIN Objects |-> Objects[i] ]
        BY <1>1, <1>2, ExtCtor
    <1>5. Objects = [ i \in DOMAIN Objects |-> Objects[i] ]
        BY <1>3, <1>4, Z3
    <1>6. QED
        BY <1>5, Z3

LEMMA SliceSweep ==
    ASSUME NEW o, NEW doc, NEW t,
           DOMAIN Objects \subseteq Id,
           DOMAIN doc = { i \in DOMAIN Objects : i.origin = o },
           \A i \in DOMAIN doc : Objects[i] = doc[i],
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address,
           \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id,
           \A k \in DOMAIN doc :
               \A a \in doc[k].promise.callbacks :
                   a \in DOMAIN Objects => a \in DOMAIN doc,
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
    PROVE  Store(Plant(Objects, o, Sweep(doc, t).doc),
                 Deliver(outbox, Sweep(doc, t).sends)) \in P!Swept(t)
PROOF
    <1> DEFINE base == Objects
    <1>1. CbLocal(doc, base)
        BY Z3 DEF CbLocal, base
    <1>2. base = [ i \in DOMAIN base |-> base[i] ]
        BY ObjEta, Z3 DEF base
    <1>3. base = Objects
        BY Z3 DEF base
    <1>4. HIDE DEF Sweep, Plant, Deliver, Store
    <1>5. QED
        BY <1>1, <1>2, <1>3, SweepIn, Isa

=============================================================================
