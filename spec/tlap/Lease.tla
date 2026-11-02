------------------------------ MODULE Lease -------------------------------
(* A lease pass is one due step per acquired id, in any order. The image is
   first-order so the induction does not instantiate a proof-local operator. *)
EXTENDS Gen

LEMMA ProjectId ==
    ASSUME NEW obj, NEW t,
           \/ obj.promise.state /= "pending"
           \/ ~(obj.promise.timeoutAt <= t)
    PROVE  P!Project(obj, t) = obj
PROOF
    BY Zenon DEF P!Project

LeaseBody(obj, t) ==
    [obj EXCEPT !.task.state          = "pending",
                !.task.pid            = NoPid,
                !.task.ttl            = NoTime,
                !.task.leaseTimeoutAt = NoTime,
                !.task.retryTimeoutAt = t]

DueL(o, t) ==
    { j \in DOMAIN o :
        /\ o[j].task.state = "acquired"
        /\ o[j].task.leaseTimeoutAt /= NoTime
        /\ o[j].task.leaseTimeoutAt <= t
        /\ P!Project(o[j], t).promise.state = "pending" }

LEMMA LeaseMember ==
    ASSUME NEW o, NEW b, NEW t, NEW i \in DOMAIN o,
           i \in DueL(o, t)
    PROVE  Store(P!Write(o, i, LeaseBody(o[i], t)), b) \in P!DueLease(o, b, t)
PROOF
    BY Isa DEF Store, DueL, LeaseBody, P!DueLease, P!Write, NoTime, P!NoTime

LEMMA InDue1L ==
    ASSUME NEW o, NEW b, NEW t, NEW st \in P!DueLease(o, b, t)
    PROVE  st \in D1(o, b, t)
PROOF
    BY DEF D1, P!Due1

ImgL(o, T, t) ==
    IF T = {} THEN o
    ELSE [ i \in DOMAIN o |-> IF i \in T THEN LeaseBody(o[i], t) ELSE o[i] ]

LEMMA LeaseSubset ==
    ASSUME NEW o, NEW t
    PROVE  DueL(o, t) \subseteq DOMAIN o
PROOF
    BY DEF DueL

LEMMA LeaseBound ==
    ASSUME NEW base, NEW t, DOMAIN base \subseteq Id
    PROVE  /\ IsFiniteSet(DueL(base, t))
           /\ Cardinality(DueL(base, t)) \in 0 .. P!MaxSweep
PROOF
    <1>1. DueL(base, t) \subseteq Id
        BY LeaseSubset, Z3
    <1>2. IsFiniteSet(Id) /\ Cardinality(Id) <= P!MaxSweep /\ P!MaxSweep \in Nat
        BY FiniteOrigin, FiniteRest, IdFinite, SweepCap
    <1>3. /\ IsFiniteSet(DueL(base, t))
          /\ Cardinality(DueL(base, t)) <= Cardinality(Id)
        BY <1>1, <1>2, FS_Subset
    <1>4. Cardinality(Id) \in Nat /\ Cardinality(DueL(base, t)) \in Nat
        BY <1>2, <1>3, FS_CardinalityType
    <1>5. QED
        BY <1>2, <1>3, <1>4, Z3

LEMMA LeaseAt ==
    ASSUME NEW o, NEW T, NEW t, NEW x,
           x \in DOMAIN o, x \notin T, T \subseteq DOMAIN o
    PROVE  /\ x \in DOMAIN ImgL(o, T, t)
           /\ ImgL(o, T, t)[x] = o[x]
PROOF
    <1>1. CASE T = {}
        BY <1>1 DEF ImgL
    <1>2. CASE T # {}
        <2> DEFINE body ==
                [ i \in DOMAIN o |-> IF i \in T THEN LeaseBody(o[i], t) ELSE o[i] ]
        <2>1. ImgL(o, T, t) = body
            BY <1>2 DEF ImgL, body
        <2>2. DOMAIN body = DOMAIN o
            BY DomCtor DEF body
        <2>3. QED
            BY <1>2, <2>1, <2>2, Z3 DEF body
    <1>3. QED
        BY <1>1, <1>2

LEMMA LeaseBulk ==
    ASSUME NEW o, NEW T, NEW t, NEW x,
           x \in DOMAIN o, x \notin T, T \subseteq DOMAIN o
    PROVE  P!Write(ImgL(o, T, t), x, LeaseBody(o[x], t))
              = ImgL(o, T \cup {x}, t)
PROOF
    <1> DEFINE proj == LeaseBody(o[x], t)
    <1>1. T \cup {x} # {}
        BY Z3
    <1>2. ImgL(o, T \cup {x}, t)
            = [ i \in DOMAIN o |-> IF i \in T \cup {x} THEN LeaseBody(o[i], t) ELSE o[i] ]
        BY <1>1 DEF ImgL
    <1>3. CASE T = {}
        <2> DEFINE e(i) == IF i = x THEN proj ELSE o[i]
        <2> DEFINE g(i) == IF i \in {x} THEN LeaseBody(o[i], t) ELSE o[i]
        <2>1. ImgL(o, T, t) = o
            BY <1>3 DEF ImgL
        <2>2. P!Write(o, x, proj) = [i \in (DOMAIN o) \cup {x} |-> e(i)]
            BY DEF e, proj, P!Write
        <2>3. (DOMAIN o) \cup {x} = DOMAIN o
            <3>1. \A y : y \in (DOMAIN o) \cup {x} <=> y \in DOMAIN o
                BY Z3
            <3>2. QED
                BY <3>1, IsaWithSetExtensionality
        <2>4. [ i \in DOMAIN o |-> IF i \in {x} THEN LeaseBody(o[i], t) ELSE o[i] ]
                = [ i \in DOMAIN o |-> g(i) ]
            BY DEF g
        <2>5. \A i \in DOMAIN o : e(i) = g(i)
            BY Z3 DEF e, g, proj
        <2>6. P!Write(o, x, proj)
                = [ i \in DOMAIN o |-> IF i \in {x} THEN LeaseBody(o[i], t) ELSE o[i] ]
            BY <2>2, <2>3, <2>4, <2>5, ExtCtor
        <2>7. T \cup {x} = {x}
            BY <1>3
        <2>8. QED
            BY <1>2, <1>3, <2>1, <2>6, <2>7
    <1>4. CASE T # {}
        <2> DEFINE cur ==
                [ i \in DOMAIN o |-> IF i \in T THEN LeaseBody(o[i], t) ELSE o[i] ]
        <2> DEFINE e(i) == IF i = x THEN proj ELSE cur[i]
        <2> DEFINE g(i) == IF i \in T \cup {x} THEN LeaseBody(o[i], t) ELSE o[i]
        <2>1. ImgL(o, T, t) = cur
            BY <1>4 DEF ImgL, cur
        <2>2. DOMAIN cur = DOMAIN o
            BY DomCtor DEF cur
        <2>3. \A i \in DOMAIN o : cur[i] = IF i \in T THEN LeaseBody(o[i], t) ELSE o[i]
            BY Z3 DEF cur
        <2>4. P!Write(cur, x, proj) = [i \in (DOMAIN cur) \cup {x} |-> e(i)]
            BY DEF e, proj, P!Write
        <2>5. (DOMAIN cur) \cup {x} = DOMAIN o
            <3>1. \A y : y \in (DOMAIN cur) \cup {x} <=> y \in DOMAIN o
                BY <2>2, Z3
            <3>2. QED
                BY <3>1, IsaWithSetExtensionality
        <2>6. \A i \in DOMAIN o : e(i) = g(i)
            BY <2>3, Z3 DEF e, g, proj
        <2>7. P!Write(cur, x, proj) = [i \in DOMAIN o |-> g(i)]
            BY <2>4, <2>5, <2>6, ExtCtor
        <2>8. QED
            BY <1>2, <2>1, <2>7 DEF g
    <1>5. QED
        BY <1>3, <1>4

LEMMA LeaseReach ==
    ASSUME NEW base, NEW box, NEW t, DOMAIN base \subseteq Id
    PROVE  ReachN(base, box, t, ImgL(base, DueL(base, t), t), box,
                  Cardinality(DueL(base, t)))
PROOF
    <1> DEFINE Due == DueL(base, t)
    <1> DEFINE Closed(T) ==
            \/ T \notin SUBSET Due
            \/ ReachN(base, box, t, ImgL(base, T, t), box, Cardinality(T))
    <1>1. IsFiniteSet(Due)
        BY LeaseBound DEF Due
    <1>2. Closed({})
        <2>1. ImgL(base, {}, t) = base
            BY DEF ImgL
        <2>2. Cardinality({}) = 0
            BY FS_EmptySet
        <2>3. ReachN(base, box, t, base, box, 0)
            BY ReachZero
        <2>4. QED
            BY <2>1, <2>2, <2>3, Z3 DEF Closed
    <1>3. ASSUME NEW T, NEW x, IsFiniteSet(T), Closed(T), x \notin T
          PROVE  Closed(T \cup {x})
        <2>1. CASE T \cup {x} \notin SUBSET Due
            BY <2>1 DEF Closed
        <2>2. CASE T \cup {x} \in SUBSET Due
            <3>1. /\ T \subseteq Due
                  /\ x \in Due
                  /\ x \notin T
                  /\ T \subseteq DOMAIN base
                  /\ x \in DOMAIN base
                BY <1>3, <2>2, LeaseSubset, Z3 DEF Due
            <3>2. ReachN(base, box, t, ImgL(base, T, t), box, Cardinality(T))
                BY <1>3, <3>1, Z3 DEF Closed
            <3>3. Cardinality(T) \in Nat /\ Cardinality(T \cup {x}) = Cardinality(T) + 1
                BY <1>3, FS_CardinalityType, FS_AddElement, Z3
            <3> DEFINE cur == ImgL(base, T, t)
            <3>4. /\ x \in DOMAIN cur
                  /\ cur[x] = base[x]
                BY <3>1, LeaseAt, Z3 DEF cur
            <3>5. x \in DueL(cur, t)
                BY <3>1, <3>4, Zenon DEF Due, DueL
            <3>6. Store(P!Write(cur, x, LeaseBody(cur[x], t)), box)
                    \in P!DueLease(cur, box, t)
                BY <3>4, <3>5, LeaseMember
            <3>7. LeaseBody(cur[x], t) = LeaseBody(base[x], t)
                BY <3>4, Z3 DEF LeaseBody
            <3>8. Store(P!Write(cur, x, LeaseBody(base[x], t)), box)
                    \in D1(cur, box, t)
                BY <3>6, <3>7, InDue1L, Z3
            <3>9. P!Write(cur, x, LeaseBody(base[x], t)) = ImgL(base, T \cup {x}, t)
                BY <3>1, LeaseBulk, Z3 DEF cur
            <3>10. ReachN(base, box, t, ImgL(base, T \cup {x}, t), box,
                          Cardinality(T) + 1)
                BY <3>2, <3>3, <3>8, <3>9, ReachAppend, Z3
            <3>11. QED
                BY <2>2, <3>3, <3>10 DEF Closed
        <2>3. QED
            BY <2>1, <2>2
    <1>4. Closed(Due)
        <2>1. HIDE DEF Closed
        <2>2. QED
            BY ONLY <1>1, <1>2, <1>3, FS_Induction, Isa
    <1>5. QED
        BY <1>4 DEF Closed, Due

===============================================================================
