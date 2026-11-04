----------------------------- MODULE SweepSent -----------------------------
(* Delivering one origin's sweep sends posts the box the abstract retry
   chain reaches: listeners from the whole-store image, retries from the
   lease image. *)
EXTENDS DueBox

LEMMA SameDeliver ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW box,
           DOMAIN base \subseteq Id,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           base = [ i \in DOMAIN base |-> base[i] ],
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address,
           \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id,
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
                ldB == ImgL(cbB, exp, t)
                ldD == ImgL(cbD, exp, t)
                rset ==
                    { j \in DOMAIN ldD :
                        ldD[j].task.state = "pending"
                        /\ ldD[j].task.retryTimeoutAt <= t }
            IN  Deliver(box, Sweep(doc, t).sends)
                  = BoxAt(BoxN(box, imB, pairs, t), ldB, rset)
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
    <1> DEFINE ldB == ImgL(cbB, exp, t)
    <1> DEFINE ldD == ImgL(cbD, exp, t)
    <1> DEFINE rset ==
            { j \in DOMAIN ldD :
                ldD[j].task.state = "pending"
                /\ ldD[j].task.retryTimeoutAt <= t }
    <1> DEFINE tdoc == SweepTimeoutAt(doc, t).doc
    <1>1. DOMAIN doc \subseteq DOMAIN base /\ DOMAIN doc \subseteq Id
        BY Zenon
    <1>2. S = { i \in DOMAIN doc :
                  /\ doc[i].promise.state = "pending"
                  /\ doc[i].promise.timeoutAt <= t }
        BY DEF S
    <1>3. tdoc = imD
        BY <1>2, TimeoutDoc DEF tdoc, imD
    <1>4. TDoc(doc, t) = tdoc
        BY DEF TDoc, tdoc
    <1>5. DueN(TDoc(doc, t), t) = pairs
        BY <1>3, <1>4 DEF pairs
    <1>6. Deliver(box, Sweep(doc, t).sends)
            = BoxAt(BoxN(box, TDoc(doc, t), DueN(TDoc(doc, t), t), t),
                    EDoc(doc, t), DueR(EDoc(doc, t), t))
        BY <1>1, SweepDueR
    <1>7. BoxN(box, TDoc(doc, t), DueN(TDoc(doc, t), t), t)
            = BoxN(box, imD, pairs, t)
        BY <1>3, <1>4, <1>5, Zenon DEF BoxN
    <1>8. LET S ==
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
        BY ExpireIs
    <1>9. ExpireDoc(doc, t) = ldD
        BY <1>8 DEF S, imD, pairs, docL, calls, cbD, exp, ldD
    <1>10. EDoc(doc, t) = ExpireDoc(doc, t)
        BY DEF EDoc, TDoc, ExpireDoc
    <1>11. { i \in DOMAIN ExpireDoc(doc, t) :
               ExpireDoc(doc, t)[i].task.state = "pending"
               /\ ExpireDoc(doc, t)[i].task.retryTimeoutAt <= t }
              = DueR(ExpireDoc(doc, t), t)
        BY ExpireDue
    <1>12. rset = DueR(ldD, t)
        BY <1>9, <1>11 DEF rset, DueR
    <1>13. DueR(EDoc(doc, t), t) = rset
        BY <1>9, <1>10, <1>12 DEF DueR
    <1>14. Deliver(box, Sweep(doc, t).sends)
             = BoxAt(BoxN(box, imD, pairs, t), ldD, rset)
        BY <1>6, <1>7, <1>9, <1>10, <1>13, Zenon DEF BoxAt
    <1>15. S \subseteq DOMAIN doc /\ S \subseteq DOMAIN base
        BY <1>1 DEF S
    <1>16. DOMAIN imD = DOMAIN doc /\ DOMAIN imB = DOMAIN base
        BY <1>15, ImageDom DEF imD, imB
    <1>17. \A k \in DOMAIN imD : imB[k] = imD[k]
        BY <1>1, <1>15, AgreeImage DEF imB, imD
    <1>18. pairs \subseteq [id : DOMAIN imD, address : Address]
        BY DueNIn DEF pairs
    <1>19. DOMAIN imD \subseteq DOMAIN imB
        BY <1>1, <1>16, Zenon
    <1>20. BoxN(box, imB, pairs, t) = BoxN(box, imD, pairs, t)
        <2> HIDE DEF S, imB, imD, pairs, mid, docL, calls, cbB, cbD,
                       exp, ldB, ldD, rset, tdoc, BoxN
        <2>1. ASSUME NEW bb, NEW aa, NEW dd, NEW P,
                     bb = box, aa = imB, dd = imD, P = pairs,
                     P \subseteq [id : DOMAIN dd, address : Address],
                     DOMAIN dd \subseteq DOMAIN aa,
                     \A k \in DOMAIN dd : aa[k] = dd[k]
              PROVE  BoxN(bb, aa, P, t) = BoxN(bb, dd, P, t)
            BY <2>1, SameBoxN, Z3, Isa
        <2>2. QED
            BY <1>17, <1>18, <1>19, <2>1, Zenon
    <1>21. Deliver(box, Sweep(doc, t).sends)
             = BoxAt(BoxN(box, imB, pairs, t), ldD, rset)
        BY <1>14, <1>20, Zenon
    <1>22. DOMAIN docL = DOMAIN imD /\ DOMAIN mid = DOMAIN imB
        BY DomImgN DEF docL, mid, imD, imB, pairs
    <1>23. DOMAIN docL \subseteq DOMAIN mid
        BY <1>1, <1>16, <1>22, Zenon
    <1>24. \A k \in DOMAIN docL : mid[k] = docL[k]
        BY <1>17, <1>19, AgreeImgN DEF imB, imD, docL, mid, pairs
    <1>25. DOMAIN cbD = DOMAIN docL /\ DOMAIN cbB = DOMAIN mid
        BY DomImgC DEF cbD, cbB, docL, mid, calls
    <1>26. DOMAIN cbD \subseteq DOMAIN cbB
        BY <1>23, <1>25, Zenon
    <1>27. \A k \in DOMAIN cbD : cbB[k] = cbD[k]
        BY <1>23, <1>24, AgreeImgC DEF mid, docL, cbB, cbD, calls
    <1>28. exp \subseteq DOMAIN cbD
        BY DEF exp
    <1>29. \A k \in DOMAIN ImgL(cbD, exp, t) :
              ImgL(cbB, exp, t)[k] = ImgL(cbD, exp, t)[k]
        BY <1>26, <1>27, <1>28, AgreeImgL, Zenon, Isa
    <1>30. \A k \in DOMAIN ldD : ldB[k] = ldD[k]
        BY <1>29 DEF ldB, ldD
    <1>31. DOMAIN ldD = DOMAIN cbD /\ DOMAIN ldB = DOMAIN cbB
        BY DomImgL DEF ldD, ldB, cbD, cbB, exp
    <1>32. DOMAIN ldD \subseteq DOMAIN ldB
        BY <1>26, <1>31, Zenon
    <1>33. rset \subseteq DOMAIN ldD
        BY DEF rset
    <1>34. BoxAt(BoxN(box, imB, pairs, t), ldB, rset)
             = BoxAt(BoxN(box, imB, pairs, t), ldD, rset)
        <2> DEFINE posted == BoxN(box, imB, pairs, t)
        <2> HIDE DEF S, imB, imD, pairs, mid, docL, calls, cbB, cbD,
                       exp, ldB, ldD, rset, tdoc, BoxN, BoxAt, posted
        <2>1. rset \subseteq DOMAIN ldD
            BY <1>33
        <2>2. DOMAIN ldD \subseteq DOMAIN ldB
            BY <1>32
        <2>3. \A k \in DOMAIN ldD : ldB[k] = ldD[k]
            BY <1>30
        <2>4. ASSUME NEW bb, NEW aa, NEW dd, NEW T,
                     bb = posted, aa = ldB, dd = ldD, T = rset,
                     T \subseteq DOMAIN dd,
                     DOMAIN dd \subseteq DOMAIN aa,
                     \A k \in DOMAIN dd : aa[k] = dd[k]
              PROVE  BoxAt(bb, aa, T) = BoxAt(bb, dd, T)
            BY <2>4, SameBoxAt, Z3, Isa
        <2>5. BoxAt(posted, ldB, rset) = BoxAt(posted, ldD, rset)
            BY <2>1, <2>2, <2>3, <2>4, Z3
        <2>6. QED
            BY <2>5 DEF posted
    <1>35. Deliver(box, Sweep(doc, t).sends)
             = BoxAt(BoxN(box, imB, pairs, t), ldB, rset)
        BY <1>21, <1>34
    <1>36. QED
        BY <1>35 DEF S, imB, imD, pairs, mid, docL, calls, cbB, cbD,
                     exp, ldB, ldD, rset

(* One origin's sweep, planted and posted, is one bounded abstract sweep. *)
LEMMA SweepSent ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW box,
           DOMAIN base \subseteq Id,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           base = [ i \in DOMAIN base |-> base[i] ],
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address,
           \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id,
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
                ldB == ImgL(cbB, exp, t)
                ldD == ImgL(cbD, exp, t)
                rset ==
                    { j \in DOMAIN ldD :
                        ldD[j].task.state = "pending"
                        /\ ldD[j].task.retryTimeoutAt <= t }
                n == Cardinality(S) + Cardinality(pairs)
                       + Cardinality(calls) + Cardinality(exp)
                       + Cardinality(rset)
            IN  /\ ReachN(base, box, t,
                          Plant(base, o, Sweep(doc, t).doc),
                          Deliver(box, Sweep(doc, t).sends),
                          n)
                /\ n \in 0 .. P!MaxSweep
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
    <1> DEFINE ldB == ImgL(cbB, exp, t)
    <1> DEFINE ldD == ImgL(cbD, exp, t)
    <1> DEFINE rset ==
            { j \in DOMAIN ldD :
                ldD[j].task.state = "pending"
                /\ ldD[j].task.retryTimeoutAt <= t }
    <1> DEFINE n ==
            Cardinality(S) + Cardinality(pairs) + Cardinality(calls)
              + Cardinality(exp) + Cardinality(rset)
    <1>1. S = { i \in DOMAIN doc :
                  doc[i].promise.state = "pending"
                  /\ doc[i].promise.timeoutAt <= t }
        BY DEF S
    <1>2. LET S ==
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
              ldB == ImgL(cbB, exp, t)
              ldD == ImgL(cbD, exp, t)
              rset ==
                { j \in DOMAIN ldD :
                    ldD[j].task.state = "pending"
                    /\ ldD[j].task.retryTimeoutAt <= t }
          IN  Plant(base, o, Sweep(doc, t).doc) = ImgR(ldB, rset, t)
        BY PlantOff
    <1>3. Plant(base, o, Sweep(doc, t).doc) = ImgR(ldB, rset, t)
        BY <1>2 DEF S, imB, imD, pairs, mid, docL, calls, cbB, cbD,
                    exp, ldB, ldD, rset
    <1>4. ReachN(base, box, t,
                 ImgR(ldB, rset, t),
                 BoxAt(BoxN(box, imB, pairs, t), ldB, rset),
                 n)
        BY <1>1, RetryJoin, Isa DEF S, imB, imD, pairs, mid, docL, calls,
                                  cbB, cbD, exp, ldB, ldD, rset, n
    <1>5. ReachN(base, box, t,
                 Plant(base, o, Sweep(doc, t).doc),
                 BoxAt(BoxN(box, imB, pairs, t), ldB, rset),
                 n)
        BY <1>3, <1>4, Zenon
    <1>6. DOMAIN doc \subseteq DOMAIN base /\ DOMAIN doc \subseteq Id
        BY Zenon
    <1>7. S \subseteq DOMAIN doc
        BY DEF S
    <1>8. S \subseteq DOMAIN base
        BY <1>6, <1>7, Zenon
    <1>9. S \subseteq Id
        BY <1>6, <1>7, Zenon
    <1>10. DOMAIN imD = DOMAIN doc /\ DOMAIN imB = DOMAIN base
        BY <1>7, <1>8, ImageDom DEF imD, imB
    <1>11. pairs \subseteq [id : DOMAIN imD, address : Address]
        BY DueNIn DEF pairs
    <1>12. pairs \subseteq [id : Id, address : Address]
        <2>1. DOMAIN imD \subseteq Id
            BY <1>6, <1>10, Zenon
        <2>2. ASSUME NEW p \in pairs
              PROVE  p \in [id : Id, address : Address]
            <3>1. p \in [id : DOMAIN imD, address : Address]
                BY <1>11, <2>2
            <3>2. p.id \in DOMAIN imD /\ p.address \in Address
                BY <3>1, Z3
            <3>3. p.id \in Id
                BY <2>1, <3>2, Zenon
            <3>4. p = [id |-> p.id, address |-> p.address]
                BY <3>1, RecPair
            <3>5. QED
                BY <3>2, <3>3, <3>4, Z3
        <2>3. QED
            BY <2>2
    <1>13. DOMAIN docL = DOMAIN imD /\ DOMAIN mid = DOMAIN imB
        BY DomImgN DEF docL, mid, imD, imB, pairs
    <1>14. DOMAIN docL \subseteq Id
        BY <1>6, <1>10, <1>13, Zenon
    <1>15. calls \subseteq [id : DOMAIN docL, awaiter : Id]
        BY AwSub DEF calls
    <1>16. calls \subseteq [id : Id, awaiter : Id]
        <2>1. ASSUME NEW p \in calls
              PROVE  p \in [id : Id, awaiter : Id]
            <3>1. p \in [id : DOMAIN docL, awaiter : Id]
                BY <1>15, <2>1
            <3>2. p.id \in DOMAIN docL /\ p.awaiter \in Id
                BY <3>1, Z3
            <3>3. p.id \in Id
                BY <1>14, <3>2, Zenon
            <3>4. p = [id |-> p.id, awaiter |-> p.awaiter]
                BY <3>1, RecAw
            <3>5. QED
                BY <3>2, <3>3, <3>4, Z3
        <2>2. QED
            BY <2>1
    <1>17. DOMAIN cbD = DOMAIN docL /\ DOMAIN cbB = DOMAIN mid
        BY DomImgC DEF cbD, cbB, docL, mid, calls
    <1>18. exp \subseteq DOMAIN cbD
        BY DEF exp
    <1>19. exp \subseteq Id
        BY <1>14, <1>17, <1>18, Zenon
    <1>20. DOMAIN ldD = DOMAIN cbD /\ DOMAIN ldB = DOMAIN cbB
        BY DomImgL DEF ldD, ldB, cbD, cbB, exp
    <1>21. rset \subseteq DOMAIN ldD
        BY DEF rset
    <1>22. rset \subseteq Id
        BY <1>14, <1>17, <1>20, <1>21, Zenon
    <1>23. n \in 0 .. P!MaxSweep
        BY <1>9, <1>12, <1>16, <1>19, <1>22, SweepBudget DEF n
    <1>24. LET S ==
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
                ldB == ImgL(cbB, exp, t)
                ldD == ImgL(cbD, exp, t)
                rset ==
                    { j \in DOMAIN ldD :
                        ldD[j].task.state = "pending"
                        /\ ldD[j].task.retryTimeoutAt <= t }
          IN  Deliver(box, Sweep(doc, t).sends)
                = BoxAt(BoxN(box, imB, pairs, t), ldB, rset)
        BY SameDeliver
    <1>25. Deliver(box, Sweep(doc, t).sends)
             = BoxAt(BoxN(box, imB, pairs, t), ldB, rset)
        BY <1>24 DEF S, imB, imD, pairs, mid, docL, calls, cbB, cbD,
                     exp, ldB, ldD, rset
    <1>26. ReachN(base, box, t,
                  Plant(base, o, Sweep(doc, t).doc),
                  Deliver(box, Sweep(doc, t).sends),
                  n)
        BY <1>5, <1>25, Zenon
    <1>27. QED
        BY <1>23, <1>26 DEF S, imB, imD, pairs, mid, docL, calls, cbB, cbD,
                             exp, ldB, ldD, rset, n

(* At the live store and outbox, that sweep is inside the abstract closure. *)
LEMMA SweepIn ==
    ASSUME NEW base, NEW o, NEW doc, NEW t, NEW box,
           DOMAIN base \subseteq Id,
           DOMAIN doc = { i \in DOMAIN base : i.origin = o },
           \A i \in DOMAIN doc : base[i] = doc[i],
           base = [ i \in DOMAIN base |-> base[i] ],
           \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address,
           \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id,
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
                   doc[k].promise.state = "pending",
           base = Objects,
           box = outbox
    PROVE  Store(Plant(base, o, Sweep(doc, t).doc),
                 Deliver(box, Sweep(doc, t).sends)) \in P!Swept(t)
PROOF
    <1>1. LET S ==
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
                ldB == ImgL(cbB, exp, t)
                ldD == ImgL(cbD, exp, t)
                rset ==
                    { j \in DOMAIN ldD :
                        ldD[j].task.state = "pending"
                        /\ ldD[j].task.retryTimeoutAt <= t }
                n == Cardinality(S) + Cardinality(pairs)
                       + Cardinality(calls) + Cardinality(exp)
                       + Cardinality(rset)
          IN  /\ ReachN(base, box, t,
                        Plant(base, o, Sweep(doc, t).doc),
                        Deliver(box, Sweep(doc, t).sends),
                        n)
              /\ n \in 0 .. P!MaxSweep
        BY SweepSent
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
    <1> DEFINE ldB == ImgL(cbB, exp, t)
    <1> DEFINE ldD == ImgL(cbD, exp, t)
    <1> DEFINE rset ==
            { j \in DOMAIN ldD :
                ldD[j].task.state = "pending"
                /\ ldD[j].task.retryTimeoutAt <= t }
    <1> DEFINE n ==
            Cardinality(S) + Cardinality(pairs) + Cardinality(calls)
              + Cardinality(exp) + Cardinality(rset)
    <1> DEFINE os == Plant(base, o, Sweep(doc, t).doc)
    <1> DEFINE b == Deliver(box, Sweep(doc, t).sends)
    <1>2. /\ ReachN(base, box, t, os, b, n)
          /\ n \in 0 .. P!MaxSweep
        BY <1>1 DEF S, imB, imD, pairs, mid, docL, calls, cbB, cbD,
                     exp, ldB, ldD, rset, n, os, b
    <1>3. Store(os, b) \in F(base, box, t, P!MaxSweep)[P!MaxSweep]
        <2>1. ASSUME NEW oo, NEW bb, NEW nn,
                     oo = os, bb = b, nn = n,
                     nn \in 0 .. P!MaxSweep,
                     ReachN(base, box, t, oo, bb, nn)
              PROVE  Store(oo, bb) \in F(base, box, t, P!MaxSweep)[P!MaxSweep]
            BY <2>1, ReachIn
        <2>2. QED
            BY <1>2, <2>1, Zenon
    <1>4. P!Swept(t) = F(Objects, outbox, t, P!MaxSweep)[P!MaxSweep]
        BY SweptIs
    <1>5. F(base, box, t, P!MaxSweep)[P!MaxSweep] = P!Swept(t)
        BY <1>4, Zenon
    <1>6. Store(os, b) \in P!Swept(t)
        BY <1>3, <1>5, Zenon
    <1>7. QED
        BY <1>6 DEF os, b

=============================================================================
