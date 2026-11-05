----------------------------- MODULE ApplyStep -----------------------------
(* A placed origin document is the slice of the store. The sweep closure
   is stated on that slice; this lemma only records the slice. *)
EXTENDS PlaceJoin

LEMMA OriginSlice ==
    ASSUME Placed, NEW o \in Origin
    PROVE  LET doc == docs[o]
            IN  /\ DOMAIN Objects \subseteq Id
                /\ DOMAIN doc = { i \in DOMAIN Objects : i.origin = o }
                /\ \A i \in DOMAIN doc : Objects[i] = doc[i]
                /\ \A k \in DOMAIN doc : doc[k].promise.listeners \subseteq Address
                /\ \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id
                /\ \A k \in DOMAIN doc :
                      \A a \in doc[k].promise.callbacks :
                          a \in DOMAIN Objects => a \in DOMAIN doc
                /\ \A k \in DOMAIN doc :
                      doc[k].task.state = "acquired" =>
                        /\ doc[k].task.leaseTimeoutAt /= NoTime
                        /\ doc[k].promise.state = "pending"
                /\ \A k \in DOMAIN doc :
                      doc[k].task.state = "pending" =>
                        /\ doc[k].task.retryTimeoutAt /= NoTime
                        /\ doc[k].promise.state = "pending"
                /\ \A k \in DOMAIN doc :
                      doc[k].task.state = "suspended" =>
                        doc[k].promise.state = "pending"
PROOF
    <1> DEFINE doc == docs[o]
    <1> DEFINE U == UNION { DOMAIN docs[p] : p \in Origin }
    <1>1. DOMAIN docs = Origin /\ DocOk(doc) /\ Home(doc, o)
        BY Z3 DEF Placed, doc
    <1>2. DOMAIN doc \subseteq { i \in Id : i.origin = o }
        BY <1>1 DEF Home, doc
    <1>3. DOMAIN Objects = UNION { DOMAIN docs[q] : q \in Origin }
        BY DomCtor, Isa DEF Objects
    <1>4. U = UNION { DOMAIN docs[q] : q \in Origin }
        BY Z3 DEF U
    <1>5. DOMAIN Objects = U
        BY <1>3, <1>4, Z3
    <1>6. ASSUME NEW p \in Origin
          PROVE  \A i \in DOMAIN docs[p] : i.origin = p /\ i \in Id
        <2>1. Home(docs[p], p)
            BY <1>6 DEF Placed
        <2>2. QED
            BY <2>1 DEF Home
    <1>7. U \subseteq Id
        BY <1>6, Z3 DEF U
    <1>8. DOMAIN Objects \subseteq Id
        BY <1>5, <1>7, Z3
    <1>9. ASSUME NEW i \in U
          PROVE  Objects[i] = docs[i.origin][i]
        BY <1>5, <1>9, AppCtor, Isa DEF Objects, U
    <1>10. \A i \in DOMAIN doc : i \in U /\ i.origin = o /\ Objects[i] = doc[i]
        BY <1>1, <1>2, <1>9, Z3 DEF doc, U
    <1>11. { i \in DOMAIN Objects : i.origin = o } \subseteq DOMAIN doc
        BY <1>5, <1>6, Z3 DEF doc, U
    <1>12. DOMAIN doc \subseteq { i \in DOMAIN Objects : i.origin = o }
        BY <1>5, <1>10, Z3
    <1>13. DOMAIN doc = { i \in DOMAIN Objects : i.origin = o }
        BY <1>11, <1>12, Z3
    <1>14. \A i \in DOMAIN doc : Objects[i] = doc[i]
        BY <1>10, Z3
    <1>15. \A k \in DOMAIN doc :
              /\ doc[k].promise.callbacks \subseteq DOMAIN doc
              /\ doc[k].promise.listeners \subseteq Address
              /\ (doc[k].task.state = "acquired" =>
                    /\ doc[k].task.leaseTimeoutAt /= NoTime
                    /\ doc[k].task.ttl \in Ttl
                    /\ doc[k].promise.state = "pending")
              /\ (doc[k].task.state = "pending" =>
                    /\ doc[k].task.retryTimeoutAt /= NoTime
                    /\ doc[k].promise.state = "pending")
              /\ (doc[k].task.state = "suspended" =>
                    doc[k].promise.state = "pending")
        BY <1>1 DEF doc, DocOk, Guard
    <1>16. \A k \in DOMAIN doc : doc[k].promise.callbacks \subseteq Id
        BY <1>2, <1>15, Z3
    <1>17. \A k \in DOMAIN doc :
              \A a \in doc[k].promise.callbacks :
                  a \in DOMAIN Objects => a \in DOMAIN doc
        BY <1>15, Z3
    <1>18. QED
        BY <1>8, <1>13, <1>14, <1>15, <1>16, <1>17, Z3 DEF doc

=============================================================================
