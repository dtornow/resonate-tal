----------------------------- MODULE PlaceJoin -----------------------------
(* The queue says which document a perform step will write. That document
   is the handler applied to the sweep, so the write keeps Placed once the
   event is one the handler knows and the origin is an origin. *)
EXTENDS Shape, PerformInv

LEMMA HeadAt ==
    ASSUME NEW seq,
           seq \in Seq(Range(seq)),
           seq # << >>
    PROVE  Head(seq) = seq[1] /\ 1 \in DOMAIN seq
PROOF
    <1>1. Head(seq) = seq[1]
        BY Z3 DEF Head
    <1>2. Len(seq) \in Nat \ {0}
        BY EmptySeq, Z3
    <1>3. DOMAIN seq = 1 .. Len(seq)
        BY LenProperties, Z3
    <1>4. 1 \in DOMAIN seq
        BY <1>2, <1>3, Z3
    <1>5. QED
        BY <1>1, <1>4, Z3

LEMMA HeadBody ==
    ASSUME NEW seq, NEW docb, NEW sent,
           seq \in Seq(Range(seq)),
           seq # << >>,
           Docs(seq, docb, sent),
           Head(seq).tag = "PutDocument"
    PROVE  Head(seq).body = docb
PROOF
    <1>1. Head(seq) = seq[1] /\ 1 \in DOMAIN seq
        BY HeadAt, Z3
    <1>2. seq[1].tag = "PutDocument"
        BY <1>1, Z3
    <1>3. seq[1].body = docb
        BY <1>1, <1>2, Z3 DEF Docs
    <1>4. QED
        BY <1>1, <1>3, Z3

LEMMA ImageDoc ==
    ASSUME NEW st
    PROVE  Image(st).doc
              = Handle(st.ev, Sweep(st.expect, st.at).doc, st.at).doc
PROOF
    <1>1. HIDE DEF Sweep, Handle
    <1>2. Image(st) =
            LET ev    == st.ev
                t     == st.at
                exp   == st.expect
                swept == Sweep(exp, t)
                out   == Handle(ev, swept.doc, t)
            IN  [doc |-> out.doc, sends |-> swept.sends \o out.sends]
        BY ONLY DEF Image
    <1>3. QED
        BY <1>2, Z3

LEMMA PutFromMatch ==
    ASSUME Placed, Queued,
           NEW r \in DOMAIN steps,
           PerformPut(r),
           steps[r].ev \in Event,
           steps[r].ev.tag \in HandleTag,
           OriginOf(steps[r].ev) \in Origin
    PROVE  Placed'
PROOF
    <1> DEFINE e == Head(steps[r].pending)
    <1> DEFINE o == OriginOf(steps[r].ev)
    <1>1. now \in Nat
        BY Z3 DEF Queued
    <1>2. steps[r].phase = "perform"
        BY Z3 DEF PerformPut
    <1>3. Match(steps[r], now)
        BY <1>2, Z3 DEF Queued
    <1>4. steps[r].at \in 0 .. now
        BY <1>3, Z3 DEF Match
    <1>5. steps[r].pending \in Seq(Range(steps[r].pending))
          /\ Docs(steps[r].pending, Image(steps[r]).doc, Image(steps[r]).sends)
        BY <1>3, Z3 DEF Match
    <1>6. steps[r].pending # << >> /\ e.tag = "PutDocument"
        BY PutWrite, Z3 DEF e, PerformPut
    <1>7. e.body = Image(steps[r]).doc
        BY <1>5, <1>6, HeadBody, Z3 DEF e
    <1>8. Image(steps[r]).doc
            = Handle(steps[r].ev,
                     Sweep(steps[r].expect, steps[r].at).doc,
                     steps[r].at).doc
        BY ImageDoc, Z3
    <1>9. e.body = Handle(steps[r].ev,
                          Sweep(steps[r].expect, steps[r].at).doc,
                          steps[r].at).doc
        BY <1>7, <1>8, Z3
    <1>10. HIDE DEF Sweep, Handle, PerformPut, Image
    <1>11. o \in Origin /\ e = Head(steps[r].pending)
        BY Z3 DEF e, o
    <1>12. QED
        BY <1>1, <1>4, <1>9, <1>11, PutKeeps, Isa DEF e, o

LEMMA PlaceWhen ==
    ASSUME Placed, Queued, [Next]_vars,
           \A r \in DOMAIN steps :
                PerformPut(r) =>
                    /\ steps[r].ev \in Event
                    /\ steps[r].ev.tag \in HandleTag
                    /\ OriginOf(steps[r].ev) \in Origin
    PROVE  Placed'
PROOF
    <1>1. CASE \A r \in DOMAIN steps : ~PerformPut(r)
        BY <1>1, PlaceQuiet, Z3
    <1>2. CASE \E r \in DOMAIN steps : PerformPut(r)
        <2>1. PICK r \in DOMAIN steps : PerformPut(r)
            BY <1>2, Z3
        <2>2. steps[r].ev \in Event
              /\ steps[r].ev.tag \in HandleTag
              /\ OriginOf(steps[r].ev) \in Origin
            BY <2>1, Z3
        <2>3. QED
            BY <2>1, <2>2, PutFromMatch, Z3
    <1>3. QED
        BY <1>1, <1>2, Z3

=============================================================================
