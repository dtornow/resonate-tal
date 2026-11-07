----------------------------- MODULE CallDoc -----------------------------
(* The callback pass of one document is the image of that document's due
   pairs, once projection is already the identity and every callback names
   an id. *)
EXTENDS Here

LEMMA WakeIs ==
    ASSUME NEW obj, NEW src, NEW t
    PROVE  Wake(obj, src, t) = P!WakeSuspended(obj, src, t)
PROOF
    BY ONLY DEF Wake, P!WakeSuspended, NoTime, P!NoTime

LEMMA AddIs ==
    ASSUME NEW obj, NEW R
    PROVE  AddResumes(obj, R) = P!UnionResumes(obj, R)
PROOF
    BY ONLY DEF AddResumes, P!UnionResumes

LEMMA DropIsClear ==
    ASSUME NEW obj
    PROVE  DropCallbacks(obj) = P!WithoutCallbacks(obj, obj.promise.callbacks)
PROOF
    <1>1. obj.promise.callbacks \ obj.promise.callbacks = {}
        BY Z3
    <1>2. QED
        BY <1>1, Zenon DEF DropCallbacks, P!WithoutCallbacks

LEMMA SameCalls ==
    ASSUME NEW doc, NEW t,
           \A i \in DOMAIN doc : P!Project(doc[i], t) = doc[i]
    PROVE  DueC(doc, t)
              = { x \in [id : { i \in DOMAIN doc :
                                  doc[i].promise.state /= "pending" },
                         awaiter : Id] :
                    x.awaiter \in doc[x.id].promise.callbacks }
PROOF
    <1> DEFINE non == { i \in DOMAIN doc : doc[i].promise.state /= "pending" }
    <1> DEFINE got ==
            { x \in [id : non, awaiter : Id] :
                x.awaiter \in doc[x.id].promise.callbacks }
    <1>1. \A j \in DOMAIN doc :
            P!Project(doc[j], t).promise.state = doc[j].promise.state
        <2> SUFFICES ASSUME NEW j \in DOMAIN doc
                     PROVE  P!Project(doc[j], t).promise.state
                               = doc[j].promise.state
            OBVIOUS
        <2>1. P!Project(doc[j], t) = doc[j]
            OBVIOUS
        <2>2. QED
            BY <2>1
    <1>2. IdsC(doc, t) = non
        BY <1>1, Z3 DEF IdsC, non
    <1>3. QED
        BY <1>2 DEF DueC, got

LEMMA DrpMem ==
    ASSUME NEW j, NEW S, NEW aw
    PROVE  aw \in Drp(j, S) <=> \E p \in S : p.id = j /\ p.awaiter = aw
PROOF
    BY ONLY DEF Drp

LEMMA SrcMem ==
    ASSUME NEW j, NEW S, NEW aw
    PROVE  aw \in Src(j, S) <=> \E p \in S : p.awaiter = j /\ p.id = aw
PROOF
    BY ONLY DEF Src

LEMMA SrcSame ==
    ASSUME NEW w, NEW S
    PROVE  Src(w, S) = { x.id : x \in { y \in S : y.awaiter = w } }
PROOF
    BY ONLY DEF Src

LEMMA CallSub ==
    ASSUME NEW non, NEW doc, NEW S,
           S = { x \in [id : non, awaiter : Id] :
                   x.awaiter \in doc[x.id].promise.callbacks }
    PROVE  S \subseteq [id : non, awaiter : Id]
PROOF
    BY Z3

LEMMA InCall ==
    ASSUME NEW non, NEW doc, NEW S, NEW x,
           S = { y \in [id : non, awaiter : Id] :
                   y.awaiter \in doc[y.id].promise.callbacks }
    PROVE  x \in S <=> x \in [id : non, awaiter : Id]
                      /\ x.awaiter \in doc[x.id].promise.callbacks
PROOF
    BY Z3

LEMMA DrpOut ==
    ASSUME NEW j, NEW non, NEW S,
           j \notin non,
           S \subseteq [id : non, awaiter : Id]
    PROVE  Drp(j, S) = {}
PROOF
    <1>1. \A aw : aw \notin Drp(j, S)
        <2> SUFFICES ASSUME NEW aw
                     PROVE  aw \notin Drp(j, S)
            OBVIOUS
        <2>1. ASSUME \E p \in S : p.id = j /\ p.awaiter = aw
              PROVE  FALSE
            <3>1. PICK p \in S : p.id = j /\ p.awaiter = aw
                BY <2>1
            <3>2. p \in [id : non, awaiter : Id]
                BY <3>1
            <3>3. p.id \in non
                BY <3>2, Z3
            <3>4. QED
                BY <3>1, <3>3
        <2>2. QED
            BY <2>1, DrpMem
    <1>2. QED
        BY <1>1, Z3

LEMMA DrpAll ==
    ASSUME NEW doc, NEW j, NEW non, NEW S,
           j \in non,
           non \subseteq DOMAIN doc,
           doc[j].promise.callbacks \subseteq Id,
           S = { x \in [id : non, awaiter : Id] :
                   x.awaiter \in doc[x.id].promise.callbacks }
    PROVE  Drp(j, S) = doc[j].promise.callbacks
PROOF
    <1> DEFINE cbs == doc[j].promise.callbacks
    <1>1. \A aw : aw \in Drp(j, S) <=> aw \in cbs
        <2> SUFFICES ASSUME NEW aw
                     PROVE  aw \in Drp(j, S) <=> aw \in cbs
            OBVIOUS
        <2> DEFINE rec == [id |-> j, awaiter |-> aw]
        <2>1. aw \in Drp(j, S) <=> \E p \in S : p.id = j /\ p.awaiter = aw
            BY DrpMem
        <2>2. rec.id = j /\ rec.awaiter = aw
            BY DEF rec
        <2>3. ASSUME aw \in cbs
              PROVE  aw \in Drp(j, S)
            <3>1. aw \in Id
                BY <2>3 DEF cbs
            <3>2. rec \in [id : non, awaiter : Id]
                BY <3>1, Z3 DEF rec
            <3>3. rec.awaiter \in doc[rec.id].promise.callbacks
                BY <2>2, <2>3 DEF cbs
            <3>4. rec \in S
                BY <3>2, <3>3, InCall
            <3>5. \E p \in S : p.id = j /\ p.awaiter = aw
                BY <2>2, <3>4 DEF rec
            <3>6. QED
                BY <2>1, <3>5
        <2>4. ASSUME aw \in Drp(j, S)
              PROVE  aw \in cbs
            <3>1. PICK p \in S : p.id = j /\ p.awaiter = aw
                BY <2>1, <2>4
            <3>2. p.awaiter \in doc[p.id].promise.callbacks
                BY <3>1, InCall
            <3>3. QED
                BY <3>1, <3>2 DEF cbs
        <2>5. QED
            BY <2>3, <2>4
    <1>2. QED
        BY <1>1, SetExtensionality DEF cbs

LEMMA SrcNonempty ==
    ASSUME NEW j, NEW S
    PROVE  Src(j, S) /= {} <=> \E x \in S : x.awaiter = j
PROOF
    <1>1. ASSUME Src(j, S) /= {}
          PROVE  \E x \in S : x.awaiter = j
        <2>1. PICK aw \in Src(j, S) : TRUE
            BY <1>1
        <2>2. \E p \in S : p.awaiter = j /\ p.id = aw
            BY <2>1, SrcMem
        <2>3. QED
            BY <2>2
    <1>2. ASSUME \E x \in S : x.awaiter = j
          PROVE  Src(j, S) /= {}
        <2>1. PICK x \in S : x.awaiter = j
            BY <1>2
        <2>2. x.id \in Src(j, S)
            BY <2>1, SrcMem
        <2>3. QED
            BY <2>2
    <1>3. QED
        BY <1>1, <1>2

LEMMA ImgAwait ==
    ASSUME NEW S, NEW j
    PROVE  j \in { x.awaiter : x \in S } <=> \E x \in S : x.awaiter = j
PROOF
    BY Z3

LEMMA AwakeIff ==
    ASSUME NEW S, NEW dom, NEW j,
           j \in dom
    PROVE  j \in ({ x.awaiter : x \in S } \cap dom) <=> Src(j, S) /= {}
PROOF
    <1>1. j \in ({ x.awaiter : x \in S } \cap dom) <=> j \in { x.awaiter : x \in S }
        BY Z3
    <1>2. QED
        BY <1>1, ImgAwait, SrcNonempty

LEMMA ClearedWhen ==
    ASSUME NEW o, NEW Q, NEW j
    PROVE  Cleared(o, Q, j)
              = (LET g == Drp(j, Q)
                 IN  IF g = {} THEN o[j] ELSE P!WithoutCallbacks(o[j], g))
PROOF
    BY ONLY Isa DEF Cleared

LEMMA WokenWhen ==
    ASSUME NEW obj, NEW srcs, NEW t
    PROVE  Woken(obj, srcs, t)
              = IF srcs = {} THEN obj
                ELSE IF obj.task.state \in {"none", "fulfilled"} THEN obj
                ELSE IF obj.task.state = "suspended"
                     THEN P!WakeSuspended(obj, srcs, t)
                     ELSE P!UnionResumes(obj, srcs)
PROOF
    BY ONLY DEF Woken

LEMMA StepSame ==
    ASSUME NEW obj, NEW src, NEW t, NEW awake,
           awake <=> src /= {}
    PROVE  Woken(obj, src, t)
              = IF ~awake \/ obj.task.state \in {"none", "fulfilled"} THEN obj
                ELSE IF obj.task.state = "suspended" THEN Wake(obj, src, t)
                ELSE AddResumes(obj, src)
PROOF
    <1>1. Woken(obj, src, t)
            = IF src = {} THEN obj
              ELSE IF obj.task.state \in {"none", "fulfilled"} THEN obj
              ELSE IF obj.task.state = "suspended"
                   THEN P!WakeSuspended(obj, src, t)
                   ELSE P!UnionResumes(obj, src)
        BY WokenWhen
    <1>2. Wake(obj, src, t) = P!WakeSuspended(obj, src, t)
        BY WakeIs
    <1>3. AddResumes(obj, src) = P!UnionResumes(obj, src)
        BY AddIs
    <1>4. CASE src = {}
        BY <1>1, <1>4
    <1>5. CASE src /= {} /\ obj.task.state \in {"none", "fulfilled"}
        BY <1>1, <1>5
    <1>6. CASE src /= {} /\ obj.task.state = "suspended"
        <2>1. obj.task.state \notin {"none", "fulfilled"}
            BY <1>6, Z3
        <2>2. QED
            BY <1>1, <1>2, <1>6, <2>1
    <1>7. CASE src /= {}
             /\ obj.task.state \notin {"none", "fulfilled"}
             /\ obj.task.state /= "suspended"
        BY <1>1, <1>3, <1>7
    <1>8. QED
        BY <1>4, <1>5, <1>6, <1>7

LEMMA CallAtDoc ==
    ASSUME NEW doc, NEW t, NEW j, NEW non, NEW due,
           j \in DOMAIN doc,
           non = { i \in DOMAIN doc : doc[i].promise.state /= "pending" },
           due = { x \in [id : non, awaiter : Id] :
                     x.awaiter \in doc[x.id].promise.callbacks },
           doc[j].promise.callbacks \subseteq Id
    PROVE  BodyC(doc, due, j, t)
              = LET struck ==
                    IF doc[j].promise.state /= "pending"
                       /\ doc[j].promise.callbacks /= {}
                    THEN DropCallbacks(doc[j])
                    ELSE doc[j]
                    resumes == { x.id : x \in { y \in due : y.awaiter = j } }
                    woken   == { x.awaiter : x \in due } \cap DOMAIN doc
                IN  IF j \notin woken \/ struck.task.state \in {"none", "fulfilled"}
                    THEN struck
                    ELSE IF struck.task.state = "suspended"
                         THEN Wake(struck, resumes, t)
                         ELSE AddResumes(struck, resumes)
PROOF
    <1> DEFINE struck ==
            IF doc[j].promise.state /= "pending"
               /\ doc[j].promise.callbacks /= {}
            THEN DropCallbacks(doc[j])
            ELSE doc[j]
    <1> DEFINE resumes == { x.id : x \in { y \in due : y.awaiter = j } }
    <1> DEFINE woken == { x.awaiter : x \in due } \cap DOMAIN doc
    <1>1. due \subseteq [id : non, awaiter : Id]
        BY CallSub
    <1>2. non \subseteq DOMAIN doc
        BY Z3
    <1>3. resumes = Src(j, due)
        BY SrcSame DEF resumes
    <1>4. j \in woken <=> Src(j, due) /= {}
        BY AwakeIff DEF woken
    <1>5. Cleared(doc, due, j) = struck
        <2>1. CASE doc[j].promise.state = "pending"
            <3>1. j \notin non
                BY <2>1, Z3
            <3>2. Drp(j, due) = {}
                BY <1>1, <3>1, DrpOut
            <3>3. Cleared(doc, due, j) = doc[j]
                BY <3>2, ClearedWhen
            <3>4. struck = doc[j]
                BY <2>1 DEF struck
            <3>5. QED
                BY <3>3, <3>4
        <2>2. CASE doc[j].promise.state /= "pending"
                 /\ doc[j].promise.callbacks = {}
            <3>1. j \in non
                BY <2>2, Z3
            <3>2. Drp(j, due) = doc[j].promise.callbacks
                BY <1>2, <3>1, DrpAll
            <3>3. Drp(j, due) = {}
                BY <2>2, <3>2
            <3>4. Cleared(doc, due, j) = doc[j]
                BY <3>3, ClearedWhen
            <3>5. struck = doc[j]
                BY <2>2 DEF struck
            <3>6. QED
                BY <3>4, <3>5
        <2>3. CASE doc[j].promise.state /= "pending"
                 /\ doc[j].promise.callbacks /= {}
            <3>1. j \in non
                BY <2>3, Z3
            <3>2. Drp(j, due) = doc[j].promise.callbacks
                BY <1>2, <3>1, DrpAll
            <3>3. Drp(j, due) /= {}
                BY <2>3, <3>2
            <3>4. Cleared(doc, due, j) = P!WithoutCallbacks(doc[j], Drp(j, due))
                BY <3>3, ClearedWhen
            <3>5. DropCallbacks(doc[j]) = P!WithoutCallbacks(doc[j], doc[j].promise.callbacks)
                BY DropIsClear
            <3>6. struck = DropCallbacks(doc[j])
                BY <2>3 DEF struck
            <3>7. QED
                BY <3>2, <3>4, <3>5, <3>6
        <2>4. QED
            BY <2>1, <2>2, <2>3
    <1>6. BodyC(doc, due, j, t) = Woken(struck, resumes, t)
        BY <1>3, <1>5 DEF BodyC
    <1>7. j \in woken <=> resumes /= {}
        BY <1>3, <1>4
    <1>8. Woken(struck, resumes, t)
            = IF j \notin woken \/ struck.task.state \in {"none", "fulfilled"}
              THEN struck
              ELSE IF struck.task.state = "suspended" THEN Wake(struck, resumes, t)
              ELSE AddResumes(struck, resumes)
        <2> DEFINE on == j \in woken
        <2>1. on <=> resumes /= {}
            BY <1>7 DEF on
        <2>2. Woken(struck, resumes, t)
                = IF ~on \/ struck.task.state \in {"none", "fulfilled"}
                  THEN struck
                  ELSE IF struck.task.state = "suspended" THEN Wake(struck, resumes, t)
                  ELSE AddResumes(struck, resumes)
            BY ONLY <2>1, StepSame DEF StepSame
        <2>3. ~on <=> j \notin woken
            BY DEF on
        <2>4. QED
            BY <2>2, <2>3
    <1>9. QED
        BY <1>6, <1>8 DEF struck, resumes, woken

LEMMA SweepCallEq ==
    ASSUME NEW doc, NEW t
    PROVE  LET S ==
                { x \in [id : { i \in DOMAIN doc :
                                  doc[i].promise.state /= "pending" },
                         awaiter : Id] :
                    x.awaiter \in doc[x.id].promise.callbacks }
                Resumes(w) == { x.id : x \in { y \in S : y.awaiter = w } }
                Woken == { x.awaiter : x \in S } \cap DOMAIN doc
           IN  SweepCallbacks(doc, t).doc
                 = IF S = {} THEN doc
                   ELSE [ i \in DOMAIN doc |->
                            LET struck ==
                                    IF doc[i].promise.state /= "pending"
                                       /\ doc[i].promise.callbacks /= {}
                                    THEN DropCallbacks(doc[i])
                                    ELSE doc[i]
                            IN  IF i \notin Woken
                                   \/ struck.task.state \in {"none", "fulfilled"}
                                THEN struck
                                ELSE IF struck.task.state = "suspended"
                                     THEN Wake(struck, Resumes(i), t)
                                     ELSE AddResumes(struck, Resumes(i)) ]
PROOF
    BY ONLY DEF SweepCallbacks

LEMMA CallDoc ==
    ASSUME NEW doc, NEW t,
           \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id,
           \A k \in DOMAIN doc : P!Project(doc[k], t) = doc[k]
    PROVE  SweepCallbacks(doc, t).doc = ImgC(doc, DueC(doc, t), t)
PROOF
    <1> DEFINE non == { i \in DOMAIN doc : doc[i].promise.state /= "pending" }
    <1> DEFINE due ==
            { x \in [id : non, awaiter : Id] :
                x.awaiter \in doc[x.id].promise.callbacks }
    <1> DEFINE Resumes(w) == { x.id : x \in { y \in due : y.awaiter = w } }
    <1> DEFINE Woken == { x.awaiter : x \in due } \cap DOMAIN doc
    <1>1. DueC(doc, t) = due
        BY SameCalls DEF non, due
    <1>2. SweepCallbacks(doc, t).doc
            = IF due = {} THEN doc
              ELSE [ i \in DOMAIN doc |->
                       LET struck ==
                               IF doc[i].promise.state /= "pending"
                                  /\ doc[i].promise.callbacks /= {}
                               THEN DropCallbacks(doc[i])
                               ELSE doc[i]
                       IN  IF i \notin Woken
                              \/ struck.task.state \in {"none", "fulfilled"}
                           THEN struck
                           ELSE IF struck.task.state = "suspended"
                                THEN Wake(struck, Resumes(i), t)
                                ELSE AddResumes(struck, Resumes(i)) ]
        BY SweepCallEq DEF non, due, Resumes, Woken
    <1>3. CASE due = {}
        <2>1. ImgC(doc, DueC(doc, t), t) = doc
            BY <1>1, <1>3 DEF ImgC
        <2>2. QED
            BY <1>2, <1>3, <2>1
    <1>4. CASE due # {}
        <2> DEFINE im == [ i \in DOMAIN doc |-> BodyC(doc, due, i, t) ]
        <2>1. ImgC(doc, DueC(doc, t), t) = im
            BY <1>1, <1>4 DEF ImgC, im
        <2>2. \A j \in DOMAIN doc :
                (LET struck ==
                       IF doc[j].promise.state /= "pending"
                          /\ doc[j].promise.callbacks /= {}
                       THEN DropCallbacks(doc[j])
                       ELSE doc[j]
                     resumes == { x.id : x \in { y \in due : y.awaiter = j } }
                     woken   == { x.awaiter : x \in due } \cap DOMAIN doc
                 IN  IF j \notin woken \/ struck.task.state \in {"none", "fulfilled"}
                     THEN struck
                     ELSE IF struck.task.state = "suspended"
                          THEN Wake(struck, resumes, t)
                          ELSE AddResumes(struck, resumes))
                  = BodyC(doc, due, j, t)
            <3> SUFFICES ASSUME NEW j \in DOMAIN doc
                         PROVE  (LET struck ==
                                       IF doc[j].promise.state /= "pending"
                                          /\ doc[j].promise.callbacks /= {}
                                       THEN DropCallbacks(doc[j])
                                       ELSE doc[j]
                                     resumes == { x.id : x \in { y \in due : y.awaiter = j } }
                                     woken   == { x.awaiter : x \in due } \cap DOMAIN doc
                                 IN  IF j \notin woken
                                        \/ struck.task.state \in {"none", "fulfilled"}
                                     THEN struck
                                     ELSE IF struck.task.state = "suspended"
                                          THEN Wake(struck, resumes, t)
                                          ELSE AddResumes(struck, resumes))
                                  = BodyC(doc, due, j, t)
                OBVIOUS
            <3>1. doc[j].promise.callbacks \subseteq Id
                OBVIOUS
            <3>2. QED
                BY <3>1, CallAtDoc DEF non, due
        <2>3. [ i \in DOMAIN doc |->
                  LET struck ==
                          IF doc[i].promise.state /= "pending"
                             /\ doc[i].promise.callbacks /= {}
                          THEN DropCallbacks(doc[i])
                          ELSE doc[i]
                  IN  IF i \notin Woken
                         \/ struck.task.state \in {"none", "fulfilled"}
                      THEN struck
                      ELSE IF struck.task.state = "suspended"
                           THEN Wake(struck, Resumes(i), t)
                           ELSE AddResumes(struck, Resumes(i)) ]
                = im
            BY <2>2, ExtCtor DEF im, Resumes, Woken
        <2>4. QED
            BY <1>2, <1>4, <2>1, <2>3
    <1>5. QED
        BY <1>3, <1>4

===============================================================================
