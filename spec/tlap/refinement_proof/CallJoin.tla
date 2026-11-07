------------------------------ MODULE CallJoin -----------------------------
(* One callback step, proved outside the induction. Clearing a callback
   commutes with a wake, and a second source unions onto the first. *)
EXTENDS Callback

WakeOne(obj, src, t) ==
    IF obj.task.state \in {"none", "fulfilled"} THEN obj
    ELSE IF obj.task.state = "suspended" THEN P!WakeSuspended(obj, src, t)
    ELSE P!UnionResumes(obj, src)

LEMMA RecBuild ==
    ASSUME NEW i, NEW w, NEW x,
           x = [id |-> i, awaiter |-> w]
    PROVE  /\ x.id = i
           /\ x.awaiter = w
           /\ x = [id |-> x.id, awaiter |-> x.awaiter]
PROOF
    BY Isa

LEMMA WokenOne ==
    ASSUME NEW obj, NEW src, NEW t, src # {}
    PROVE  Woken(obj, src, t) = WakeOne(obj, src, t)
PROOF
    <1>1. CASE obj.task.state \in {"none", "fulfilled"}
        BY <1>1 DEF Woken, WakeOne
    <1>2. CASE obj.task.state = "suspended"
        BY <1>2 DEF Woken, WakeOne
    <1>3. CASE obj.task.state \notin {"none", "fulfilled", "suspended"}
        BY <1>3 DEF Woken, WakeOne
    <1>4. QED
        BY <1>1, <1>2, <1>3

LEMMA WakeJoin ==
    ASSUME NEW obj, NEW srcs, NEW a, NEW t
    PROVE  WakeOne(Woken(obj, srcs, t), {a}, t)
              = Woken(obj, srcs \cup {a}, t)
PROOF
    <1>1. CASE srcs = {}
        <2>1. Woken(obj, srcs, t) = obj
            BY <1>1 DEF Woken
        <2>2. srcs \cup {a} = {a} /\ {a} # {}
            BY <1>1, Zenon
        <2>3. Woken(obj, srcs \cup {a}, t) = WakeOne(obj, {a}, t)
            BY <2>2, WokenOne
        <2>4. QED
            BY <2>1, <2>2, <2>3
    <1>2. CASE srcs # {} /\ obj.task.state \in {"none", "fulfilled"}
        <2>1. Woken(obj, srcs, t) = obj
            BY <1>2 DEF Woken
        <2>2. WakeOne(obj, {a}, t) = obj
            BY <1>2 DEF WakeOne
        <2>3. srcs \cup {a} # {}
            BY <1>2, Zenon
        <2>4. Woken(obj, srcs \cup {a}, t) = obj
            BY <1>2, <2>3 DEF Woken
        <2>5. QED
            BY <2>1, <2>2, <2>4
    <1>3. CASE srcs # {} /\ obj.task.state = "suspended"
        <2> DEFINE mid == P!WakeSuspended(obj, srcs, t)
        <2>1. Woken(obj, srcs, t) = mid
            BY <1>3 DEF Woken, mid
        <2>2. mid.task.state = "pending"
            BY Zenon DEF mid, P!WakeSuspended
        <2>3. mid.task.state \notin {"none", "fulfilled", "suspended"}
            BY <2>2, Zenon
        <2>4. WakeOne(mid, {a}, t) = P!UnionResumes(mid, {a})
            BY <2>3 DEF WakeOne
        <2>5. P!UnionResumes(mid, {a}) = P!WakeSuspended(obj, srcs \cup {a}, t)
            BY WakeAdd DEF mid
        <2>6. srcs \cup {a} # {}
            BY <1>3, Zenon
        <2>7. Woken(obj, srcs \cup {a}, t) = P!WakeSuspended(obj, srcs \cup {a}, t)
            BY <1>3, <2>6 DEF Woken
        <2>8. QED
            BY <2>1, <2>4, <2>5, <2>7
    <1>4. CASE srcs # {} /\ obj.task.state \notin {"none", "fulfilled", "suspended"}
        <2> DEFINE mid == P!UnionResumes(obj, srcs)
        <2>1. Woken(obj, srcs, t) = mid
            BY <1>4 DEF Woken, mid
        <2>2. mid.task.state = obj.task.state
            BY Zenon DEF mid, P!UnionResumes
        <2>3. mid.task.state \notin {"none", "fulfilled", "suspended"}
            BY <1>4, <2>2
        <2>4. WakeOne(mid, {a}, t) = P!UnionResumes(mid, {a})
            BY <2>3 DEF WakeOne
        <2>5. P!UnionResumes(mid, {a}) = P!UnionResumes(obj, srcs \cup {a})
            BY WakeAdd DEF mid
        <2>6. srcs \cup {a} # {}
            BY <1>4, Zenon
        <2>7. Woken(obj, srcs \cup {a}, t) = P!UnionResumes(obj, srcs \cup {a})
            BY <1>4, <2>6 DEF Woken
        <2>8. QED
            BY <2>1, <2>4, <2>5, <2>7
    <1>5. QED
        BY <1>1, <1>2, <1>3, <1>4

LEMMA ClearJoinObj ==
    ASSUME NEW obj, NEW srcs, NEW a, NEW t
    PROVE  P!WithoutCallbacks(Woken(obj, srcs, t), {a})
              = Woken(P!WithoutCallbacks(obj, {a}), srcs, t)
PROOF
    <1>1. CASE srcs = {}
        <2>1. Woken(obj, srcs, t) = obj
            BY <1>1 DEF Woken
        <2>2. Woken(P!WithoutCallbacks(obj, {a}), srcs, t)
                = P!WithoutCallbacks(obj, {a})
            BY <1>1 DEF Woken
        <2>3. QED
            BY <2>1, <2>2
    <1>2. CASE srcs # {} /\ obj.task.state \in {"none", "fulfilled"}
        <2>1. Woken(obj, srcs, t) = obj
            BY <1>2 DEF Woken
        <2>2. P!WithoutCallbacks(obj, {a}).task.state = obj.task.state
            BY Zenon DEF P!WithoutCallbacks
        <2>3. Woken(P!WithoutCallbacks(obj, {a}), srcs, t)
                = P!WithoutCallbacks(obj, {a})
            BY <1>2, <2>2 DEF Woken
        <2>4. QED
            BY <2>1, <2>3
    <1>3. CASE srcs # {} /\ obj.task.state = "suspended"
        <2> DEFINE mid == P!WakeSuspended(obj, srcs, t)
        <2> DEFINE cleared == P!WithoutCallbacks(obj, {a})
        <2>1. Woken(obj, srcs, t) = mid
            BY <1>3 DEF Woken, mid
        <2>2. P!WithoutCallbacks(mid, {a}) = P!WakeSuspended(cleared, srcs, t)
            BY ClearWake DEF mid, cleared
        <2>3. cleared.task.state = "suspended"
            BY <1>3, Zenon DEF cleared, P!WithoutCallbacks
        <2>4. Woken(cleared, srcs, t) = P!WakeSuspended(cleared, srcs, t)
            BY <1>3, <2>3 DEF Woken
        <2>5. QED
            BY <2>1, <2>2, <2>4 DEF cleared
    <1>4. CASE srcs # {} /\ obj.task.state \notin {"none", "fulfilled", "suspended"}
        <2> DEFINE mid == P!UnionResumes(obj, srcs)
        <2> DEFINE cleared == P!WithoutCallbacks(obj, {a})
        <2>1. Woken(obj, srcs, t) = mid
            BY <1>4 DEF Woken, mid
        <2>2. P!WithoutCallbacks(mid, {a}) = P!UnionResumes(cleared, srcs)
            BY ClearWake DEF mid, cleared
        <2>3. cleared.task.state = obj.task.state
            BY Zenon DEF cleared, P!WithoutCallbacks
        <2>4. cleared.task.state \notin {"none", "fulfilled", "suspended"}
            BY <1>4, <2>3
        <2>5. Woken(cleared, srcs, t) = P!UnionResumes(cleared, srcs)
            BY <1>4, <2>4 DEF Woken
        <2>6. QED
            BY <2>1, <2>2, <2>5 DEF cleared
    <1>5. QED
        BY <1>1, <1>2, <1>3, <1>4

LEMMA SelfJoin ==
    ASSUME NEW obj, NEW srcs, NEW a, NEW t
    PROVE  WakeOne(P!WithoutCallbacks(Woken(obj, srcs, t), {a}), {a}, t)
              = Woken(P!WithoutCallbacks(obj, {a}), srcs \cup {a}, t)
PROOF
    <1> DEFINE cleared == P!WithoutCallbacks(obj, {a})
    <1>1. CASE srcs = {}
        <2>1. Woken(obj, srcs, t) = obj
            BY <1>1 DEF Woken
        <2>2. srcs \cup {a} = {a} /\ {a} # {}
            BY <1>1, Zenon
        <2>3. Woken(cleared, srcs \cup {a}, t) = WakeOne(cleared, {a}, t)
            BY <2>2, WokenOne DEF cleared
        <2>4. QED
            BY <2>1, <2>2, <2>3 DEF cleared
    <1>2. CASE srcs # {} /\ obj.task.state \in {"none", "fulfilled"}
        <2>1. Woken(obj, srcs, t) = obj
            BY <1>2 DEF Woken
        <2>2. cleared.task.state \in {"none", "fulfilled"}
            BY <1>2, Zenon DEF cleared, P!WithoutCallbacks
        <2>3. WakeOne(cleared, {a}, t) = cleared
            BY <2>2 DEF WakeOne, cleared
        <2>4. srcs \cup {a} # {}
            BY <1>2, Zenon
        <2>5. Woken(cleared, srcs \cup {a}, t) = cleared
            BY <2>2, <2>4 DEF Woken, cleared
        <2>6. QED
            BY <2>1, <2>3, <2>5 DEF cleared
    <1>3. CASE srcs # {} /\ obj.task.state = "suspended"
        <2> DEFINE mid == P!WakeSuspended(obj, srcs, t)
        <2> DEFINE dropped == P!WithoutCallbacks(mid, {a})
        <2>1. Woken(obj, srcs, t) = mid
            BY <1>3 DEF Woken, mid
        <2>2. dropped = P!WakeSuspended(cleared, srcs, t)
            BY ClearWake DEF mid, dropped, cleared
        <2>3. dropped.task.state = "pending"
            <3>1. P!WakeSuspended(cleared, srcs, t).task.state = "pending"
                BY Isa DEF P!WakeSuspended
            <3>2. QED
                BY <2>2, <3>1, Z3
        <2>4. dropped.task.state \notin {"none", "fulfilled", "suspended"}
            BY <2>3, Zenon
        <2>5. WakeOne(dropped, {a}, t) = P!UnionResumes(dropped, {a})
            BY <2>4 DEF WakeOne
        <2>6. P!UnionResumes(P!WakeSuspended(cleared, srcs, t), {a})
                = P!WakeSuspended(cleared, srcs \cup {a}, t)
            BY WakeAdd DEF cleared
        <2>7. srcs \cup {a} # {} /\ cleared.task.state = "suspended"
            BY <1>3, Zenon DEF cleared, P!WithoutCallbacks
        <2>8. Woken(cleared, srcs \cup {a}, t)
                = P!WakeSuspended(cleared, srcs \cup {a}, t)
            BY <2>7 DEF Woken
        <2>9. QED
            BY <2>1, <2>2, <2>5, <2>6, <2>8 DEF dropped
    <1>4. CASE srcs # {} /\ obj.task.state \notin {"none", "fulfilled", "suspended"}
        <2> DEFINE mid == P!UnionResumes(obj, srcs)
        <2> DEFINE dropped == P!WithoutCallbacks(mid, {a})
        <2>1. Woken(obj, srcs, t) = mid
            BY <1>4 DEF Woken, mid
        <2>2. dropped = P!UnionResumes(cleared, srcs)
            BY ClearWake DEF mid, dropped, cleared
        <2>3. dropped.task.state = obj.task.state
            BY <2>2, Zenon DEF dropped, cleared, P!UnionResumes, P!WithoutCallbacks
        <2>4. dropped.task.state \notin {"none", "fulfilled", "suspended"}
            BY <1>4, <2>3
        <2>5. WakeOne(dropped, {a}, t) = P!UnionResumes(dropped, {a})
            BY <2>4 DEF WakeOne
        <2>6. P!UnionResumes(P!UnionResumes(cleared, srcs), {a})
                = P!UnionResumes(cleared, srcs \cup {a})
            BY WakeAdd DEF cleared
        <2>7. srcs \cup {a} # {}
            BY <1>4, Zenon
        <2>8. cleared.task.state \notin {"none", "fulfilled", "suspended"}
            BY <1>4, Zenon DEF cleared, P!WithoutCallbacks
        <2>9. Woken(cleared, srcs \cup {a}, t) = P!UnionResumes(cleared, srcs \cup {a})
            BY <2>7, <2>8 DEF Woken
        <2>10. QED
            BY <2>1, <2>2, <2>5, <2>6, <2>9 DEF dropped
    <1>5. QED
        BY <1>1, <1>2, <1>3, <1>4

LEMMA DomImg ==
    ASSUME NEW o, NEW S, NEW t
    PROVE  DOMAIN ImgC(o, S, t) = DOMAIN o
PROOF
    <1>1. CASE S = {}
        BY <1>1 DEF ImgC
    <1>2. CASE S # {}
        <2> DEFINE fn == [k \in DOMAIN o |-> BodyC(o, S, k, t)]
        <2>1. ImgC(o, S, t) = fn
            BY <1>2 DEF ImgC, fn
        <2>2. DOMAIN fn = DOMAIN o
            BY DomCtor DEF fn
        <2>3. QED
            BY <2>1, <2>2
    <1>3. QED
        BY <1>1, <1>2

LEMMA ProjBody ==
    ASSUME NEW base, NEW S, NEW j \in DOMAIN base, NEW t,
           P!Project(base[j], t) = base[j]
    PROVE  P!Project(BodyC(base, S, j, t), t) = BodyC(base, S, j, t)
PROOF
    <1>1. \/ base[j].promise.state /= "pending"
          \/ ~(base[j].promise.timeoutAt <= t)
        BY GuardHeld
    <1>2. /\ BodyC(base, S, j, t).promise.state = base[j].promise.state
          /\ BodyC(base, S, j, t).promise.timeoutAt = base[j].promise.timeoutAt
        BY BodyPromise
    <1>3. \/ BodyC(base, S, j, t).promise.state /= "pending"
          \/ ~(BodyC(base, S, j, t).promise.timeoutAt <= t)
        BY <1>1, <1>2
    <1>4. QED
        BY <1>3, ProjectId

LEMMA WriteAs ==
    ASSUME NEW doc, NEW id, NEW obj, NEW dom,
           dom = (DOMAIN doc) \cup {id}
    PROVE  P!Write(doc, id, obj)
              = [k \in dom |-> IF k = id THEN obj ELSE doc[k]]
PROOF
    <1> DEFINE e(k) == IF k = id THEN obj ELSE doc[k]
    <1>1. P!Write(doc, id, obj) = [k \in (DOMAIN doc) \cup {id} |-> e(k)]
        BY DEF e, P!Write
    <1>2. \A k \in dom : e(k) = IF k = id THEN obj ELSE doc[k]
        BY DEF e
    <1>3. QED
        BY <1>1, <1>2, ExtCtor

LEMMA StillBody ==
    ASSUME NEW base, NEW T, NEW k, NEW i, NEW w, NEW t,
           k \in DOMAIN base, k # i, k # w
    PROVE  BodyC(base, T \cup {[id |-> i, awaiter |-> w]}, k, t)
              = BodyC(base, T, k, t)
PROOF
    <1> DEFINE x == [id |-> i, awaiter |-> w]
    <1>1. /\ x.id = i
          /\ x.awaiter = w
          /\ x = [id |-> x.id, awaiter |-> x.awaiter]
        BY RecBuild DEF x
    <1>2. Drp(k, T \cup {x}) = IF k = x.id THEN Drp(k, T) \cup {x.awaiter}
                              ELSE Drp(k, T)
        BY <1>1, DrpStep
    <1>3. Drp(k, T \cup {x}) = Drp(k, T)
        BY <1>1, <1>2
    <1>4. Src(k, T \cup {x}) = IF k = x.awaiter THEN Src(k, T) \cup {x.id}
                              ELSE Src(k, T)
        BY <1>1, SrcStep
    <1>5. Src(k, T \cup {x}) = Src(k, T)
        BY <1>1, <1>4
    <1>6. CASE Drp(k, T) = {}
        <2>1. Cleared(base, T, k) = base[k]
            BY <1>6 DEF Cleared
        <2>2. Cleared(base, T \cup {x}, k) = base[k]
            BY <1>3, <1>6 DEF Cleared
        <2>3. QED
            BY <1>5, <2>1, <2>2 DEF BodyC
    <1>7. CASE Drp(k, T) # {}
        <2>1. Cleared(base, T, k) = P!WithoutCallbacks(base[k], Drp(k, T))
            BY <1>7 DEF Cleared
        <2>2. Cleared(base, T \cup {x}, k)
                = P!WithoutCallbacks(base[k], Drp(k, T))
            BY <1>3, <1>7 DEF Cleared
        <2>3. QED
            BY <1>5, <2>1, <2>2 DEF BodyC
    <1>8. QED
        BY <1>6, <1>7

LEMMA ClearOnly ==
    ASSUME NEW base, NEW T, NEW i, NEW w, NEW t,
           i \in DOMAIN base, i # w, w \notin Drp(i, T)
    PROVE  P!WithoutCallbacks(BodyC(base, T, i, t), {w})
              = BodyC(base, T \cup {[id |-> i, awaiter |-> w]}, i, t)
PROOF
    <1> DEFINE x == [id |-> i, awaiter |-> w]
    <1> DEFINE g == Drp(i, T)
    <1> DEFINE srcs == Src(i, T)
    <1> DEFINE leaf == Cleared(base, T, i)
    <1>1. /\ x.id = i
          /\ x.awaiter = w
          /\ x = [id |-> x.id, awaiter |-> x.awaiter]
        BY RecBuild DEF x
    <1>2. Drp(i, T \cup {x}) = g \cup {w}
        BY <1>1, DrpStep DEF g
    <1>3. Src(i, T \cup {x}) = srcs
        BY <1>1, SrcStep DEF srcs
    <1>4. g \cup {w} # {}
        BY Zenon
    <1>5. Cleared(base, T \cup {x}, i) = P!WithoutCallbacks(base[i], g \cup {w})
        BY <1>2, <1>4 DEF Cleared
    <1>6. BodyC(base, T \cup {x}, i, t)
            = Woken(P!WithoutCallbacks(base[i], g \cup {w}), srcs, t)
        BY <1>3, <1>5 DEF BodyC
    <1>7. BodyC(base, T, i, t) = Woken(leaf, srcs, t)
        BY DEF BodyC, leaf, srcs
    <1>8. CASE g = {}
        <2>1. leaf = base[i]
            BY <1>8 DEF leaf, Cleared, g
        <2>2. P!WithoutCallbacks(base[i], g \cup {w})
                = P!WithoutCallbacks(base[i], {w})
            BY <1>8 DEF g
        <2>3. P!WithoutCallbacks(Woken(base[i], srcs, t), {w})
                = Woken(P!WithoutCallbacks(base[i], {w}), srcs, t)
            BY ClearJoinObj
        <2>4. QED
            BY <1>6, <1>7, <2>1, <2>2, <2>3
    <1>9. CASE g # {}
        <2>1. leaf = P!WithoutCallbacks(base[i], g)
            BY <1>9 DEF leaf, Cleared, g
        <2>2. P!WithoutCallbacks(leaf, {w})
                = P!WithoutCallbacks(base[i], g \cup {w})
            BY <2>1, ClearDrop
        <2>3. P!WithoutCallbacks(Woken(leaf, srcs, t), {w})
                = Woken(P!WithoutCallbacks(leaf, {w}), srcs, t)
            BY ClearJoinObj
        <2>4. QED
            BY <1>6, <1>7, <2>2, <2>3
    <1>10. QED
        BY <1>8, <1>9

LEMMA WakeOnly ==
    ASSUME NEW base, NEW T, NEW i, NEW w, NEW t,
           w \in DOMAIN base, w # i
    PROVE  WakeOne(BodyC(base, T, w, t), {i}, t)
              = BodyC(base, T \cup {[id |-> i, awaiter |-> w]}, w, t)
PROOF
    <1> DEFINE x == [id |-> i, awaiter |-> w]
    <1> DEFINE srcs == Src(w, T)
    <1> DEFINE leaf == Cleared(base, T, w)
    <1>1. /\ x.id = i
          /\ x.awaiter = w
          /\ x = [id |-> x.id, awaiter |-> x.awaiter]
        BY RecBuild DEF x
    <1>2. Drp(w, T \cup {x}) = Drp(w, T)
        BY <1>1, DrpStep
    <1>3. Src(w, T \cup {x}) = srcs \cup {i}
        BY <1>1, SrcStep DEF srcs
    <1>4. Cleared(base, T \cup {x}, w) = leaf
        <2>1. CASE Drp(w, T) = {}
            <3>1. leaf = base[w]
                BY <2>1 DEF leaf, Cleared
            <3>2. Cleared(base, T \cup {x}, w) = base[w]
                BY <1>2, <2>1 DEF Cleared
            <3>3. QED
                BY <3>1, <3>2
        <2>2. CASE Drp(w, T) # {}
            <3>1. leaf = P!WithoutCallbacks(base[w], Drp(w, T))
                BY <2>2 DEF leaf, Cleared
            <3>2. Cleared(base, T \cup {x}, w)
                    = P!WithoutCallbacks(base[w], Drp(w, T))
                BY <1>2, <2>2 DEF Cleared
            <3>3. QED
                BY <3>1, <3>2
        <2>3. QED
            BY <2>1, <2>2
    <1>5. BodyC(base, T, w, t) = Woken(leaf, srcs, t)
        BY DEF BodyC, leaf, srcs
    <1>6. BodyC(base, T \cup {x}, w, t) = Woken(leaf, srcs \cup {i}, t)
        BY <1>3, <1>4 DEF BodyC
    <1>7. WakeOne(Woken(leaf, srcs, t), {i}, t) = Woken(leaf, srcs \cup {i}, t)
        BY WakeJoin
    <1>8. QED
        BY <1>5, <1>6, <1>7

LEMMA SelfOnly ==
    ASSUME NEW base, NEW T, NEW i, NEW t,
           i \in DOMAIN base, i \notin Drp(i, T)
    PROVE  WakeOne(P!WithoutCallbacks(BodyC(base, T, i, t), {i}), {i}, t)
              = BodyC(base, T \cup {[id |-> i, awaiter |-> i]}, i, t)
PROOF
    <1> DEFINE x == [id |-> i, awaiter |-> i]
    <1> DEFINE g == Drp(i, T)
    <1> DEFINE srcs == Src(i, T)
    <1> DEFINE leaf == Cleared(base, T, i)
    <1>1. /\ x.id = i
          /\ x.awaiter = i
          /\ x = [id |-> x.id, awaiter |-> x.awaiter]
        BY RecBuild DEF x
    <1>2. Drp(i, T \cup {x}) = g \cup {i}
        BY <1>1, DrpStep DEF g
    <1>3. Src(i, T \cup {x}) = srcs \cup {i}
        BY <1>1, SrcStep DEF srcs
    <1>4. g \cup {i} # {}
        BY Zenon
    <1>5. Cleared(base, T \cup {x}, i) = P!WithoutCallbacks(base[i], g \cup {i})
        BY <1>2, <1>4 DEF Cleared
    <1>6. BodyC(base, T \cup {x}, i, t)
            = Woken(P!WithoutCallbacks(base[i], g \cup {i}), srcs \cup {i}, t)
        BY <1>3, <1>5 DEF BodyC
    <1>7. BodyC(base, T, i, t) = Woken(leaf, srcs, t)
        BY DEF BodyC, leaf, srcs
    <1>8. CASE g = {}
        <2>1. leaf = base[i]
            BY <1>8 DEF leaf, Cleared, g
        <2>2. P!WithoutCallbacks(base[i], g \cup {i})
                = P!WithoutCallbacks(base[i], {i})
            BY <1>8 DEF g
        <2>3. WakeOne(P!WithoutCallbacks(Woken(base[i], srcs, t), {i}), {i}, t)
                = Woken(P!WithoutCallbacks(base[i], {i}), srcs \cup {i}, t)
            BY SelfJoin
        <2>4. QED
            BY <1>6, <1>7, <2>1, <2>2, <2>3
    <1>9. CASE g # {}
        <2>1. leaf = P!WithoutCallbacks(base[i], g)
            BY <1>9 DEF leaf, Cleared, g
        <2>2. P!WithoutCallbacks(leaf, {i})
                = P!WithoutCallbacks(base[i], g \cup {i})
            BY <2>1, ClearDrop
        <2>3. WakeOne(P!WithoutCallbacks(Woken(leaf, srcs, t), {i}), {i}, t)
                = Woken(P!WithoutCallbacks(leaf, {i}), srcs \cup {i}, t)
            BY SelfJoin
        <2>4. QED
            BY <1>6, <1>7, <2>2, <2>3
    <1>10. QED
        BY <1>8, <1>9

LEMMA CallStep ==
    ASSUME NEW base, NEW T, NEW x, NEW t,
           x \in [id : DOMAIN base, awaiter : Id],
           \A j \in DOMAIN base : P!Project(base[j], t) = base[j],
           x.awaiter \notin Drp(x.id, T)
    PROVE  P!CallbackObjects(ImgC(base, T, t), x.id, x.awaiter, t)
              = ImgC(base, T \cup {x}, t)
PROOF
    <1> DEFINE i == x.id
    <1> DEFINE w == x.awaiter
    <1> DEFINE cur == ImgC(base, T, t)
    <1> DEFINE nxt == ImgC(base, T \cup {x}, t)
    <1> DEFINE clear == P!WithoutCallbacks(cur[i], {w})
    <1> DEFINE struck == P!Write(cur, i, clear)
    <1> DEFINE built == [id |-> i, awaiter |-> w]
    <1>1. i \in DOMAIN base /\ w \in Id
        BY Z3 DEF i, w
    <1>2. x = built
        BY <1>1, RecAw, Zenon DEF i, w, built
    <1>3. DOMAIN cur = DOMAIN base
        BY DomImg DEF cur
    <1>4. i \in DOMAIN cur /\ cur[i] = BodyC(base, T, i, t)
        BY <1>1, CallAt DEF cur
    <1>5. P!Project(base[i], t) = base[i]
        BY <1>1
    <1>6. P!Project(cur[i], t) = cur[i]
        BY <1>1, <1>4, <1>5, ProjBody
    <1>7. w \notin Drp(i, T)
        BY DEF i, w
    <1>8. (DOMAIN cur) \cup {i} = DOMAIN base
        BY <1>1, <1>3, Z3
    <1>9. struck = [k \in DOMAIN base |-> IF k = i THEN clear ELSE cur[k]]
        BY <1>8, WriteAs DEF struck
    <1>10. T \cup {x} # {}
        BY Zenon
    <1>11. nxt = [k \in DOMAIN base |-> BodyC(base, T \cup {x}, k, t)]
        BY <1>10 DEF nxt, ImgC
    <1>12. clear = P!WithoutCallbacks(P!Project(cur[i], t), {w})
        BY <1>6 DEF clear
    <1>13. P!CallbackObjects(cur, i, w, t)
            = IF w \notin DOMAIN cur THEN struck
              ELSE LET awaiter == P!Project(struck[w], t)
                   IN  IF awaiter.task.state \in {"none", "fulfilled"}
                          THEN P!Write(struck, w, awaiter)
                       ELSE IF awaiter.task.state = "suspended"
                          THEN P!Write(struck, w, P!WakeSuspended(awaiter, {i}, t))
                       ELSE P!Write(struck, w, P!UnionResumes(awaiter, {i}))
        BY <1>12, Zenon DEF clear, struck, P!CallbackObjects
    <1>14. CASE w \notin DOMAIN base
        <2>1. w \notin DOMAIN cur /\ i # w
            BY <1>1, <1>3, <1>14, Z3
        <2>2. P!CallbackObjects(cur, i, w, t) = struck
            BY <1>13, <2>1
        <2>3. \A k \in DOMAIN base :
                (IF k = i THEN clear ELSE cur[k])
                  = BodyC(base, T \cup {x}, k, t)
            <3> SUFFICES ASSUME NEW k \in DOMAIN base
                         PROVE  (IF k = i THEN clear ELSE cur[k])
                                   = BodyC(base, T \cup {x}, k, t)
                OBVIOUS
            <3>1. CASE k # i
                <4>1. k # w
                    BY <1>14, <3>1, Z3
                <4>2. cur[k] = BodyC(base, T, k, t)
                    BY CallAt
                <4>3. BodyC(base, T \cup {built}, k, t) = BodyC(base, T, k, t)
                    BY <3>1, <4>1, StillBody DEF built
                <4>4. BodyC(base, T \cup {x}, k, t) = BodyC(base, T \cup {built}, k, t)
                    BY <1>2, Zenon
                <4>5. QED
                    BY <3>1, <4>2, <4>3, <4>4 DEF clear
            <3>2. CASE k = i
                <4>1. clear = P!WithoutCallbacks(BodyC(base, T, i, t), {w})
                    BY <1>4 DEF clear
                <4>2. P!WithoutCallbacks(BodyC(base, T, i, t), {w})
                        = BodyC(base, T \cup {built}, i, t)
                    BY <1>1, <1>7, <2>1, ClearOnly
                <4>3. BodyC(base, T \cup {x}, i, t) = BodyC(base, T \cup {built}, i, t)
                    BY <1>2, Zenon
                <4>4. QED
                    BY <3>2, <4>1, <4>2, <4>3
            <3>3. QED
                BY <3>1, <3>2
        <2>4. [k \in DOMAIN base |-> IF k = i THEN clear ELSE cur[k]]
                = [k \in DOMAIN base |-> BodyC(base, T \cup {x}, k, t)]
            BY <2>3, ExtCtor
        <2>5. QED
            BY <1>9, <1>11, <2>2, <2>4
    <1>15. CASE w \in DOMAIN base
        <2> DEFINE awaiter == P!Project(struck[w], t)
        <2> DEFINE wake ==
                IF awaiter.task.state \in {"none", "fulfilled"} THEN awaiter
                ELSE IF awaiter.task.state = "suspended"
                     THEN P!WakeSuspended(awaiter, {i}, t)
                ELSE P!UnionResumes(awaiter, {i})
        <2>1. w \in DOMAIN cur
            BY <1>3, <1>15
        <2>2. P!CallbackObjects(cur, i, w, t) = P!Write(struck, w, wake)
            BY <1>13, <2>1 DEF awaiter, wake
        <2>3. ASSUME w # i
              PROVE  wake = BodyC(base, T \cup {built}, w, t)
            <3>1a. w # i /\ w \in DOMAIN base
                BY <1>15, <2>3
            <3>1b. w \in (DOMAIN cur) \cup {i}
                BY <1>3, <3>1a, Z3
            <3>1c. struck[w] = IF w = i THEN clear ELSE cur[w]
                BY <3>1b, WriteAt DEF struck
            <3>1. struck[w] = cur[w]
                BY <3>1a, <3>1c, Zenon
            <3>2. cur[w] = BodyC(base, T, w, t)
                BY <1>15, CallAt DEF cur
            <3>3. P!Project(base[w], t) = base[w]
                BY <1>15
            <3>4. P!Project(BodyC(base, T, w, t), t) = BodyC(base, T, w, t)
                BY <1>15, <3>3, ProjBody
            <3>5. awaiter = cur[w]
                BY <3>1, <3>2, <3>4 DEF awaiter
            <3>6. wake = WakeOne(cur[w], {i}, t)
                BY <3>5 DEF wake, WakeOne
            <3>7. WakeOne(BodyC(base, T, w, t), {i}, t)
                    = BodyC(base, T \cup {built}, w, t)
                BY <1>15, <2>3, <3>1a, WakeOnly DEF built
            <3>8. QED
                BY <3>2, <3>6, <3>7
        <2>4. ASSUME w = i
              PROVE  wake = BodyC(base, T \cup {built}, i, t)
            <3>1a. w = i /\ w \in DOMAIN base
                BY <1>15, <2>4
            <3>1b. w \in (DOMAIN cur) \cup {i}
                BY <1>3, <3>1a, Z3
            <3>1c. struck[w] = IF w = i THEN clear ELSE cur[w]
                BY <3>1b, WriteAt DEF struck
            <3>1. struck[w] = clear
                BY <3>1a, <3>1c, Zenon
            <3>2. P!Project(clear, t) = clear
                BY <1>6, ProjectClear DEF clear
            <3>3. awaiter = clear
                BY <3>1, <3>2 DEF awaiter
            <3>4. wake = WakeOne(clear, {i}, t)
                BY <3>3 DEF wake, WakeOne
            <3>5. clear = P!WithoutCallbacks(BodyC(base, T, i, t), {i})
                BY <1>4, <3>1a, Zenon DEF clear
            <3>6. i \notin Drp(i, T)
                BY <1>7, <3>1a, Zenon
            <3>6b. WakeOne(P!WithoutCallbacks(BodyC(base, T, i, t), {i}), {i}, t)
                    = BodyC(base, T \cup {built}, i, t)
                BY <1>1, <3>1a, <3>6, SelfOnly DEF built
            <3>7. QED
                BY <3>4, <3>5, <3>6b
        <2>5. \A k \in DOMAIN base :
                (IF k = w THEN wake ELSE struck[k])
                  = BodyC(base, T \cup {x}, k, t)
            <3> SUFFICES ASSUME NEW k \in DOMAIN base
                         PROVE  (IF k = w THEN wake ELSE struck[k])
                                   = BodyC(base, T \cup {x}, k, t)
                OBVIOUS
            <3>1. struck[k] = IF k = i THEN clear ELSE cur[k]
                BY <1>9, Z3
            <3>2. CASE k # i /\ k # w
                <4>1. cur[k] = BodyC(base, T, k, t)
                    BY CallAt
                <4>2. BodyC(base, T \cup {built}, k, t) = BodyC(base, T, k, t)
                    BY <3>2, StillBody DEF built
                <4>3. BodyC(base, T \cup {x}, k, t) = BodyC(base, T \cup {built}, k, t)
                    BY <1>2, Zenon
                <4>4. QED
                    BY <3>1, <3>2, <4>1, <4>2, <4>3
            <3>3. CASE k = i /\ k # w
                <4>1. P!WithoutCallbacks(BodyC(base, T, i, t), {w})
                        = BodyC(base, T \cup {built}, i, t)
                    BY <1>1, <1>7, <3>3, ClearOnly
                <4>2. clear = P!WithoutCallbacks(BodyC(base, T, i, t), {w})
                    BY <1>4 DEF clear
                <4>3. BodyC(base, T \cup {x}, i, t) = BodyC(base, T \cup {built}, i, t)
                    BY <1>2, Zenon
                <4>4. QED
                    BY <3>1, <3>3, <4>1, <4>2, <4>3
            <3>4. CASE k = w /\ k # i
                <4>1. w # i
                    BY <3>4
                <4>2. wake = BodyC(base, T \cup {built}, w, t)
                    BY <2>3, <4>1
                <4>3. BodyC(base, T \cup {x}, w, t) = BodyC(base, T \cup {built}, w, t)
                    BY <1>2, Zenon
                <4>4. QED
                    BY <3>4, <4>2, <4>3
            <3>5. CASE k = w /\ k = i
                <4>1. w = i
                    BY <3>5
                <4>2. wake = BodyC(base, T \cup {built}, i, t)
                    BY <2>4, <4>1
                <4>3. BodyC(base, T \cup {x}, i, t) = BodyC(base, T \cup {built}, i, t)
                    BY <1>2, Zenon
                <4>4. QED
                    BY <3>5, <4>2, <4>3
            <3>6. QED
                BY <3>2, <3>3, <3>4, <3>5
        <2>6. DOMAIN struck = DOMAIN base
            BY <1>9, DomCtor
        <2>7. (DOMAIN struck) \cup {w} = DOMAIN base
            BY <1>15, <2>6, Z3
        <2>8. P!Write(struck, w, wake)
                = [k \in DOMAIN base |-> IF k = w THEN wake ELSE struck[k]]
            BY <2>7, WriteAs
        <2>9. P!Write(struck, w, wake) = nxt
            BY <1>11, <2>5, <2>8, ExtCtor
        <2>10. QED
            BY <2>2, <2>9 DEF nxt
    <1>16. QED
        BY <1>14, <1>15

===============================================================================
