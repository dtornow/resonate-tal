------------------------------- MODULE Plant -------------------------------
(* Replacing one origin's document is planting that document into the store
   the protocol sees. Ids of other origins stay where they are. *)
EXTENDS CallDoc

Obj(d) ==
    [ i \in UNION { DOMAIN d[p] : p \in Origin } |-> d[i.origin][i] ]

LEMMA ObjectsAre ==
    Objects = Obj(docs) /\ Objects' = Obj(docs')
PROOF
    BY DEF Objects, Obj

LEMMA ExceptAt ==
    ASSUME NEW o \in Origin, NEW d, NEW body, NEW d2,
           DOMAIN d = Origin,
           d2 = [d EXCEPT ![o] = body]
    PROVE  /\ DOMAIN d2 = Origin
           /\ d2[o] = body
           /\ \A p \in Origin \ {o} : d2[p] = d[p]
PROOF
    BY Z3

Plant(base, o, body) ==
    [ i \in (({ j \in DOMAIN base : j.origin # o }) \cup DOMAIN body) |->
        IF i \in DOMAIN body THEN body[i] ELSE base[i] ]

LEMMA PlantFun ==
    ASSUME NEW o \in Origin, NEW d, NEW body,
           DOMAIN d = Origin,
           \A p \in Origin : \A i \in DOMAIN d[p] : i.origin = p,
           \A i \in DOMAIN body : i.origin = o
    PROVE  Obj([d EXCEPT ![o] = body]) = Plant(Obj(d), o, body)
PROOF
    <1> DEFINE d2 == [d EXCEPT ![o] = body]
    <1> DEFINE base == Obj(d)
    <1> DEFINE img == Obj(d2)
    <1> DEFINE kept == { j \in DOMAIN base : j.origin # o }
    <1> DEFINE dom == kept \cup DOMAIN body
    <1>1. /\ DOMAIN d2 = Origin
          /\ d2[o] = body
          /\ \A p \in Origin \ {o} : d2[p] = d[p]
        BY ExceptAt DEF d2
    <1>2. DOMAIN base = UNION { DOMAIN d[p] : p \in Origin }
        BY DEF base, Obj
    <1>3. DOMAIN img = UNION { DOMAIN d2[p] : p \in Origin }
        BY DEF img, Obj
    <1>4. DOMAIN img = dom
        BY <1>1, <1>2, <1>3, Z3 DEF kept, dom
    <1>5. \A i \in dom : img[i] = IF i \in DOMAIN body THEN body[i] ELSE base[i]
        BY <1>1, <1>4, Z3 DEF img, base, Obj, kept, dom
    <1>6. img = [ i \in dom |-> IF i \in DOMAIN body THEN body[i] ELSE base[i] ]
        <2>1. img = [ i \in UNION { DOMAIN d2[p] : p \in Origin } |-> d2[i.origin][i] ]
            BY DEF img, Obj
        <2>2. QED
            BY <1>3, <1>4, <1>5, <2>1, ExtCtor DEF kept, dom
    <1>7. QED
        BY <1>6 DEF Plant, kept, dom, base, img

===============================================================================
