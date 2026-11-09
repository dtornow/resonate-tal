------------------------------ MODULE Pass --------------------------------
(* A sweep of one origin takes a subset of each due set. The full-set chains
   stay as they are. Here the same induction is stated for any finite subset,
   and a listener step only needs the projection to be the identity at the
   ids that step touches. *)
EXTENDS ListenSub

LEMMA LeaseSub ==
    ASSUME NEW base, NEW box, NEW t, NEW S,
           IsFiniteSet(S),
           S \subseteq DueL(base, t)
    PROVE  ReachN(base, box, t, ImgL(base, S, t), box, Cardinality(S))
PROOF
    <1> DEFINE Due == S
    <1> DEFINE Closed(T) ==
            \/ T \notin SUBSET Due
            \/ ReachN(base, box, t, ImgL(base, T, t), box, Cardinality(T))
    <1>1. IsFiniteSet(Due)
        BY DEF Due
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
                BY <1>3, <2>2, Z3 DEF Due
            <3>1b. x \in DueL(base, t) /\ T \subseteq DueL(base, t)
                BY <3>1 DEF Due
            <3>1c. T \subseteq DOMAIN base /\ x \in DOMAIN base
                BY <3>1b, LeaseSubset, Z3
            <3>2. ReachN(base, box, t, ImgL(base, T, t), box, Cardinality(T))
                BY <1>3, <3>1, Z3 DEF Closed
            <3>3. Cardinality(T) \in Nat
                    /\ Cardinality(T \cup {x}) = Cardinality(T) + 1
                BY <1>3, FS_CardinalityType, FS_AddElement, Z3
            <3> DEFINE cur == ImgL(base, T, t)
            <3>4. /\ x \in DOMAIN cur
                  /\ cur[x] = base[x]
                BY <3>1, <3>1c, LeaseAt, Z3 DEF cur
            <3>5. x \in DueL(cur, t)
                BY <3>1b, <3>4, Zenon DEF DueL
            <3>6. Store(P!Write(cur, x, LeaseBody(cur[x], t)), box)
                    \in P!DueLease(cur, box, t)
                BY <3>4, <3>5, LeaseMember
            <3>7. LeaseBody(cur[x], t) = LeaseBody(base[x], t)
                BY <3>4, Z3 DEF LeaseBody
            <3>8. Store(P!Write(cur, x, LeaseBody(base[x], t)), box)
                    \in D1(cur, box, t)
                BY <3>6, <3>7, InDue1L, Z3
            <3>9. P!Write(cur, x, LeaseBody(base[x], t)) = ImgL(base, T \cup {x}, t)
                BY <3>1, <3>1c, LeaseBulk, Z3 DEF cur
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

LEMMA RetrySub ==
    ASSUME NEW base, NEW box, NEW t, NEW S,
           IsFiniteSet(S),
           S \subseteq DueR(base, t)
    PROVE  ReachN(base, box, t, ImgR(base, S, t), BoxAt(box, base, S),
                  Cardinality(S))
PROOF
    <1> DEFINE Due == S
    <1> DEFINE Closed(T) ==
            \/ T \notin SUBSET Due
            \/ ReachN(base, box, t, ImgR(base, T, t), BoxAt(box, base, T),
                      Cardinality(T))
    <1>1. IsFiniteSet(Due)
        BY DEF Due
    <1>2. Closed({})
        <2>1. ImgR(base, {}, t) = base
            BY DEF ImgR
        <2>2. BoxAt(box, base, {}) = box
            <3>1. Msgs(base, {}) = {}
                BY DEF Msgs
            <3>2. QED
                BY <3>1 DEF BoxAt, Posted
        <2>3. Cardinality({}) = 0
            BY FS_EmptySet
        <2>4. ReachN(base, box, t, base, box, 0)
            BY ReachZero
        <2>5. QED
            BY <2>1, <2>2, <2>3, <2>4, Z3 DEF Closed
    <1>3. ASSUME NEW T, NEW x, IsFiniteSet(T), Closed(T), x \notin T
          PROVE  Closed(T \cup {x})
        <2>1. CASE T \cup {x} \notin SUBSET Due
            BY <2>1 DEF Closed
        <2>2. CASE T \cup {x} \in SUBSET Due
            <3>1. /\ T \subseteq Due
                  /\ x \in Due
                  /\ x \notin T
                BY <1>3, <2>2, Z3 DEF Due
            <3>1b. x \in DueR(base, t) /\ T \subseteq DueR(base, t)
                BY <3>1 DEF Due
            <3>1c. T \subseteq DOMAIN base /\ x \in DOMAIN base
                BY <3>1b, RetrySubset, Z3
            <3>2. ReachN(base, box, t, ImgR(base, T, t), BoxAt(box, base, T),
                         Cardinality(T))
                BY <1>3, <3>1, Z3 DEF Closed
            <3>3. Cardinality(T) \in Nat
                    /\ Cardinality(T \cup {x}) = Cardinality(T) + 1
                BY <1>3, FS_CardinalityType, FS_AddElement, Z3
            <3> DEFINE cur == ImgR(base, T, t)
            <3> DEFINE curb == BoxAt(box, base, T)
            <3>4. /\ x \in DOMAIN cur
                  /\ cur[x] = base[x]
                BY <3>1, <3>1c, RetryAt, Z3 DEF cur
            <3>5. x \in DueR(cur, t)
                BY <3>1b, <3>4, Zenon DEF DueR
            <3>6. RetryBody(cur[x], t) = RetryBody(base[x], t)
                BY <3>4, Z3 DEF RetryBody
            <3>7. RetryMsg(cur, x) = RetryMsg(base, x)
                BY <3>4, Z3 DEF RetryMsg
            <3>8. Store(P!Write(cur, x, RetryBody(base[x], t)),
                        Post(curb, RetryMsg(base, x)))
                    \in P!DueRetry(cur, curb, t)
                BY <3>4, <3>5, <3>6, <3>7, RetryMember, Z3
            <3>9. Store(P!Write(cur, x, RetryBody(base[x], t)),
                        Post(curb, RetryMsg(base, x)))
                    \in D1(cur, curb, t)
                BY <3>8, InDue1R
            <3>10. P!Write(cur, x, RetryBody(base[x], t))
                      = ImgR(base, T \cup {x}, t)
                BY <3>1, <3>1c, RetryBulk, Z3 DEF cur
            <3>11. Post(curb, RetryMsg(base, x)) = BoxAt(box, base, T \cup {x})
                BY <3>1, <3>1c, BoxStepR DEF curb
            <3>12. ReachN(base, box, t, ImgR(base, T \cup {x}, t),
                          BoxAt(box, base, T \cup {x}), Cardinality(T) + 1)
                BY <3>2, <3>3, <3>9, <3>10, <3>11, ReachAppend, Z3
            <3>13. QED
                BY <2>2, <3>3, <3>12 DEF Closed
        <2>3. QED
            BY <2>1, <2>2
    <1>4. Closed(Due)
        <2>1. HIDE DEF Closed
        <2>2. QED
            BY ONLY <1>1, <1>2, <1>3, FS_Induction, Isa
    <1>5. QED
        BY <1>4 DEF Closed, Due

(* The projection only has to be the identity at the ids in the subset.
   After a timeout of one origin, other origins may still be due. *)
LEMMA ListenOn ==
    ASSUME NEW base, NEW box, NEW t, NEW S,
           IsFiniteSet(S),
           S \subseteq DueN(base, t),
           DOMAIN base \subseteq Id,
           \A y \in S : P!Project(base[y.id], t) = base[y.id]
    PROVE  ReachN(base, box, t,
                  ImgN(base, S),
                  BoxN(box, base, S, t),
                  Cardinality(S))
PROOF
    <1> DEFINE Due == S
    <1> DEFINE Closed(T) ==
            \/ T \notin SUBSET Due
            \/ ReachN(base, box, t, ImgN(base, T), BoxN(box, base, T, t),
                      Cardinality(T))
    <1>1. IsFiniteSet(Due)
        BY DEF Due
    <1>2. Closed({})
        <2>1. ImgN(base, {}) = base
            BY DEF ImgN
        <2>2. BoxN(box, base, {}, t) = box
            <3>1. MsgN(base, {}, t) = {}
                BY DEF MsgN
            <3>2. QED
                BY <3>1 DEF BoxN, Posted
        <2>3. Cardinality({}) = 0
            BY FS_EmptySet
        <2>4. ReachN(base, box, t, base, box, 0)
            BY ReachZero
        <2>5. QED
            BY <2>1, <2>2, <2>3, <2>4, Z3 DEF Closed
    <1>3. ASSUME NEW T, NEW x, IsFiniteSet(T), Closed(T), x \notin T
          PROVE  Closed(T \cup {x})
        <2>1. CASE T \cup {x} \notin SUBSET Due
            BY <2>1 DEF Closed
        <2>2. CASE T \cup {x} \in SUBSET Due
            <3>1. /\ T \subseteq Due
                  /\ x \in Due
                  /\ x \notin T
                BY <1>3, <2>2, Z3 DEF Due
            <3>1b. x \in DueN(base, t) /\ T \subseteq DueN(base, t)
                BY <3>1 DEF Due
            <3>1c. DueN(base, t) \subseteq [id : DOMAIN base, address : Address]
                BY PairSubset
            <3>1d. /\ T \subseteq [id : DOMAIN base, address : Address]
                   /\ x \in [id : DOMAIN base, address : Address]
                BY <3>1b, <3>1c, Z3
            <3>2. ReachN(base, box, t, ImgN(base, T), BoxN(box, base, T, t),
                         Cardinality(T))
                BY <1>3, <3>1, Z3 DEF Closed
            <3>3. Cardinality(T) \in Nat
                    /\ Cardinality(T \cup {x}) = Cardinality(T) + 1
                BY <1>3, FS_CardinalityType, FS_AddElement, Z3
            <3> DEFINE cur == ImgN(base, T)
            <3> DEFINE curb == BoxN(box, base, T, t)
            <3> DEFINE i == x.id
            <3> DEFINE a == x.address
            <3>4. i \in DOMAIN base /\ a \in Address /\ i \in Ids(base, t)
                    /\ a \in base[i].promise.listeners
                BY <3>1b, RecPair, Zenon DEF DueN, Ids
            <3>5. /\ i \in DOMAIN cur
                  /\ cur[i] = BodyN(base, T, i)
                BY <3>1d, <3>4, ListenAt, Z3 DEF cur
            <3>6. P!Project(base[i], t) = base[i]
                BY <3>1 DEF Due, i
            <3>7. base[i].promise.state /= "pending"
                BY <3>4, <3>6, GuardHeld, Zenon DEF Ids
            <3>8. a \in cur[i].promise.listeners
                <4>1. CASE Gone(i, T) = {}
                    <5>1. cur[i] = base[i]
                        BY <3>5, <4>1 DEF BodyN
                    <5>2. QED
                        BY <3>4, <5>1
                <4>2. CASE Gone(i, T) # {}
                    <5>1. cur[i] = Struck(base[i], Gone(i, T))
                        BY <3>5, <4>2 DEF BodyN
                    <5>2. a \notin Gone(i, T)
                        BY <3>1, <3>1d, RecPair, Zenon DEF Gone
                    <5>3. cur[i].promise.listeners
                            = base[i].promise.listeners \ Gone(i, T)
                        BY <5>1 DEF Struck
                    <5>4. a \in cur[i].promise.listeners
                        BY <3>4, <5>2, <5>3, Z3
                    <5>5. QED
                        BY <5>4
                <4>3. QED
                    BY <4>1, <4>2
            <3>9. P!Project(cur[i], t) = cur[i]
                <4>1. CASE Gone(i, T) = {}
                    BY <3>5, <3>6, <4>1, Z3 DEF BodyN
                <4>2. CASE Gone(i, T) # {}
                    <5>1. cur[i] = Struck(base[i], Gone(i, T))
                        BY <3>5, <4>2 DEF BodyN
                    <5>2. QED
                        BY <3>6, <5>1, ProjectDrop
                <4>3. QED
                    BY <4>1, <4>2
            <3>10. cur[i].promise.state = base[i].promise.state
                <4>1. CASE Gone(i, T) = {}
                    BY <3>5, <4>1, Z3 DEF BodyN
                <4>2. CASE Gone(i, T) # {}
                    <5>1. cur[i] = Struck(base[i], Gone(i, T))
                        BY <3>5, <4>2 DEF BodyN
                    <5>2. cur[i].promise.state = base[i].promise.state
                        BY <5>1 DEF Struck
                    <5>3. QED
                        BY <5>2
                <4>3. QED
                    BY <4>1, <4>2
            <3>11. Store(P!Write(cur, i, LBody(cur[i], a)),
                         Post(curb, UnblockMsg(cur, i, a, t)))
                      \in P!DueListener(cur, curb, t)
                BY <3>4, <3>5, <3>7, <3>8, <3>9, <3>10, ListenMember, Z3
            <3>12. UnblockMsg(cur, i, a, t) = UnblockMsg(base, i, a, t)
                BY <3>6, <3>9, <3>10, Z3 DEF UnblockMsg
            <3>13. Store(P!Write(cur, i, LBody(cur[i], a)),
                         Post(curb, UnblockMsg(base, i, a, t)))
                      \in D1(cur, curb, t)
                BY <3>11, <3>12, InDue1N, Z3
            <3>14. P!Write(cur, i, LBody(cur[i], a)) = ImgN(base, T \cup {x})
                BY <3>1, <3>1d, ListenBulk, Z3 DEF cur, i, a
            <3>15. Post(curb, UnblockMsg(base, i, a, t))
                      = BoxN(box, base, T \cup {x}, t)
                BY <3>1, <3>1d, BoxStepN, Z3 DEF curb, i, a
            <3>16. ReachN(base, box, t, ImgN(base, T \cup {x}),
                          BoxN(box, base, T \cup {x}, t), Cardinality(T) + 1)
                BY <3>2, <3>3, <3>13, <3>14, <3>15, ReachAppend, Z3
            <3>17. QED
                BY <2>2, <3>3, <3>16 DEF Closed
        <2>3. QED
            BY <2>1, <2>2
    <1>4. Closed(Due)
        <2>1. HIDE DEF Closed
        <2>2. QED
            BY ONLY <1>1, <1>2, <1>3, FS_Induction, Isa
    <1>5. QED
        BY <1>4 DEF Closed, Due

===============================================================================
