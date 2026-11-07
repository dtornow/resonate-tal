----------------------------- MODULE PerformInv -----------------------------
(* A step in phase perform still carries the document Process queued.
   The decision time is steps[r].at, the compared document is expect, and
   every PutDocument entry is Handle of the sweep of that document. The
   entry may sit behind put-timeouts, so the fact is about the whole
   sequence. Consuming the head keeps it. A miss leaves the phase. *)
EXTENDS Concrete, PendingSeq, StepFun, TLAPS

Image(st) ==
    LET ev  == st.ev
        t   == st.at
        exp == st.expect
        swept == Sweep(exp, t)
        out   == Handle(ev, swept.doc, t)
    IN  [doc |-> out.doc, sends |-> swept.sends \o out.sends]

Match(st, tm) ==
    /\ st.at \in 0 .. tm
    /\ st.pending \in Seq(Range(st.pending))
    /\ Docs(st.pending, Image(st).doc, Image(st).sends)

Queued ==
    /\ now \in Nat
    /\ \A r \in DOMAIN steps :
         steps[r].phase = "perform" => Match(steps[r], now)

StepDom == {"ev", "phase", "pending", "expect", "at"}

(* Every step record is the Fresh record, updated in place. EXCEPT reads a
   field only when that field is in the domain, so the queue proof carries
   the domain next to the phase. *)
Shaped ==
    \A r \in DOMAIN steps : DOMAIN steps[r] = StepDom

LEMMA MatchSame ==
    ASSUME NEW st, NEW tm, NEW st2, NEW tm2,
           Match(st, tm), st2 = st, tm2 = tm
    PROVE  Match(st2, tm2)
PROOF
    BY DEF Match, Image

LEMMA StutterKeeps ==
    ASSUME Queued, now' = now, steps' = steps
    PROVE  Queued'
PROOF
    BY Isa DEF Queued, Match, Image

LEMMA AddKeeps ==
    ASSUME Queued,
           NEW r,
           NEW ev,
           r \notin DOMAIN steps,
           steps' = Set(steps, r, Fresh(ev)),
           now' = now
    PROVE  Queued'
PROOF
    <1>1. now \in Nat /\ now' \in Nat
        BY DEF Queued
    <1>2. steps'[r] = Fresh(ev)
        BY Zenon DEF Set
    <1>3. Fresh(ev).phase = "process"
        BY DEF Fresh
    <1>4. DOMAIN steps' = (DOMAIN steps) \cup {r}
        BY Zenon DEF Set
    <1>5. ASSUME NEW q \in DOMAIN steps
          PROVE  steps'[q] = steps[q]
        BY <1>5, Zenon DEF Set
    <1>6. ASSUME NEW q \in DOMAIN steps', steps'[q].phase = "perform"
          PROVE  Match(steps'[q], now')
        <2>1. q # r
            BY <1>2, <1>3, <1>6, Zenon
        <2>2. q \in DOMAIN steps
            BY <1>4, <1>6, <2>1
        <2>3. steps'[q] = steps[q]
            BY <1>5, <2>2
        <2>4. steps[q].phase = "perform"
            BY <1>6, <2>3, Zenon
        <2>5. Match(steps[q], now)
            BY <2>2, <2>4 DEF Queued
        <2>6. QED
            BY <2>3, <2>5, MatchSame
    <1>7. QED
        BY <1>1, <1>6 DEF Queued

LEMMA DropKeeps ==
    ASSUME Queued,
           NEW r \in DOMAIN steps,
           steps' = Del(steps, r),
           now' = now
    PROVE  Queued'
PROOF
    <1>1. now \in Nat /\ now' \in Nat
        BY DEF Queued
    <1>2. ASSUME NEW q \in DOMAIN steps'
          PROVE  q \in DOMAIN steps /\ q # r /\ steps'[q] = steps[q]
        BY <1>2, Zenon DEF Del
    <1>3. ASSUME NEW q \in DOMAIN steps', steps'[q].phase = "perform"
          PROVE  Match(steps'[q], now')
        <2>1. q \in DOMAIN steps /\ steps'[q] = steps[q]
            BY <1>2, <1>3
        <2>2. steps[q].phase = "perform"
            BY <1>3, <2>1, Zenon
        <2>3. Match(steps[q], now)
            BY <2>1, <2>2 DEF Queued
        <2>4. QED
            BY <2>1, <2>3, MatchSame
    <1>4. QED
        BY <1>1, <1>3 DEF Queued

LEMMA TailKeeps ==
    ASSUME Queued,
           NEW r \in DOMAIN steps,
           steps[r].phase = "perform",
           steps[r].pending # << >>,
           now' = now,
           DOMAIN steps' = DOMAIN steps,
           steps'[r].ev = steps[r].ev,
           steps'[r].at = steps[r].at,
           steps'[r].expect = steps[r].expect,
           steps'[r].phase = "perform",
           steps'[r].pending = Tail(steps[r].pending),
           \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
    PROVE  Queued'
PROOF
    <1> DEFINE pend == steps[r].pending
               tail == Tail(pend)
               img  == Image(steps[r])
               st   == steps'[r]
    <1>1. now \in Nat /\ now' \in Nat
        BY DEF Queued
    <1>2. Match(steps[r], now)
        BY DEF Queued
    <1>3. pend \in Seq(Range(pend)) /\ Docs(pend, img.doc, img.sends)
        BY <1>2 DEF Match, pend, img
    <1>4. tail \in Seq(Range(tail)) /\ Docs(tail, img.doc, img.sends)
        BY <1>3, TailDoc DEF pend, tail
    <1>5. st.ev = steps[r].ev /\ st.at = steps[r].at
          /\ st.expect = steps[r].expect /\ st.pending = tail
        BY DEF st, pend, tail
    <1>6. Image(st) = img
        BY <1>5, Isa DEF Image, img
    <1>7. st.at \in 0 .. now'
        BY <1>2, <1>5 DEF Match
    <1>8. Match(st, now')
        BY <1>4, <1>5, <1>6, <1>7, Zenon DEF Match
    <1>9. ASSUME NEW q \in DOMAIN steps'
          PROVE  steps'[q].phase = "perform" => Match(steps'[q], now')
        <2>1. q \in DOMAIN steps
            BY <1>9
        <2>2. CASE q = r
            BY <1>8, <2>2 DEF st
        <2>3. CASE q # r
            <3>1. steps'[q] = steps[q]
                BY <2>1, <2>3
            <3>2. CASE steps[q].phase = "perform"
                <4>1. Match(steps[q], now)
                    BY <2>1, <3>2 DEF Queued
                <4>2. QED
                    BY <3>1, <4>1, MatchSame
            <3>3. CASE steps[q].phase # "perform"
                BY <3>1, <3>3, Zenon
            <3>4. QED
                BY <3>2, <3>3
        <2>4. QED
            BY <2>2, <2>3
    <1>10. QED
        BY <1>1, <1>9 DEF Queued

LEMMA MissKeeps ==
    ASSUME Queued,
           NEW r \in DOMAIN steps,
           now' = now,
           DOMAIN steps' = DOMAIN steps,
           steps'[r].phase = "process",
           \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
    PROVE  Queued'
PROOF
    <1>1. now \in Nat /\ now' \in Nat
        BY DEF Queued
    <1>2. ASSUME NEW q \in DOMAIN steps', steps'[q].phase = "perform"
          PROVE  Match(steps'[q], now')
        <2>1. q # r
            BY <1>2, Zenon
        <2>2. q \in DOMAIN steps
            BY <1>2, <2>1
        <2>3. steps'[q] = steps[q]
            BY <1>2, <2>1, <2>2
        <2>4. steps[q].phase = "perform"
            BY <1>2, <2>3, Zenon
        <2>5. Match(steps[q], now)
            BY <2>2, <2>4 DEF Queued
        <2>6. QED
            BY <2>3, <2>5, MatchSame
    <1>3. QED
        BY <1>1, <1>2 DEF Queued

LEMMA ClockKeeps ==
    ASSUME Queued, now' = now + 1, steps' = steps
    PROVE  Queued'
PROOF
    <1>1. now \in Nat
        BY DEF Queued
    <1>2. now' \in Nat
        BY <1>1, SMT
    <1>3. ASSUME NEW st, Match(st, now)
          PROVE  Match(st, now')
        <2>1. st.at \in 0 .. now
            BY <1>3 DEF Match
        <2>2. st.at \in 0 .. now'
            BY <1>1, <2>1, SMT
        <2>3. st.pending \in Seq(Range(st.pending))
            BY <1>3 DEF Match
        <2>4. Docs(st.pending, Image(st).doc, Image(st).sends)
            BY <1>3 DEF Match
        <2>5. QED
            BY <2>2, <2>3, <2>4 DEF Match
    <1>4. ASSUME NEW q \in DOMAIN steps', steps'[q].phase = "perform"
          PROVE  Match(steps'[q], now')
        <2>1. steps'[q] = steps[q] /\ q \in DOMAIN steps
            BY <1>4
        <2>2. steps[q].phase = "perform"
            BY <1>4, <2>1, Zenon
        <2>3. Match(steps[q], now)
            BY <2>1, <2>2 DEF Queued
        <2>4. QED
            BY <1>3, <2>1, <2>3
    <1>5. QED
        BY <1>2, <1>4 DEF Queued

LEMMA ProcessKeeps ==
    ASSUME Queued, Shaped, NEW r \in DOMAIN steps, Process(r)
    PROVE  Queued'
PROOF
    <1> DEFINE o == OriginOf(steps[r].ev)
               swept == Sweep(docs[o], now)
               out == Handle(steps[r].ev, swept.doc, now)
               final == out.doc
               puts == swept.puts \o out.puts
               dels == swept.dels \o out.dels
               sends == swept.sends \o out.sends
               pre == [n \in 1 .. Len(puts) |->
                          [tag |-> "PutTimeout", entry |-> puts[n]]]
               rec == [tag |-> "PutDocument", body |-> final, sends |-> sends]
               post == [n \in 1 .. Len(dels) |->
                           [tag |-> "DelTimeout", entry |-> dels[n]]]
               seq == (pre \o <<rec>>) \o post
               st == steps'[r]
    <1>1. now' = now
        BY DEF Process
    <1>2. now \in Nat /\ now' \in Nat
        BY <1>1 DEF Queued
    <1>3. Len(puts) \in Nat /\ Len(dels) \in Nat
        BY LenNat DEF puts, dels
    <1>4. steps' = [steps EXCEPT ![r].phase   = "perform",
                                ![r].at      = now,
                                ![r].pending = seq,
                                ![r].expect  = docs[o]]
        BY Isa DEF Process, o, swept, out, final, puts, dels, sends,
                            pre, rec, post, seq
    <1>5. /\ steps'[r].phase = "perform"
          /\ steps'[r].at = now
          /\ steps'[r].pending = seq
          /\ steps'[r].expect = docs[o]
          /\ steps'[r].ev = steps[r].ev
        <2>1. "phase" \in DOMAIN steps[r] /\ "at" \in DOMAIN steps[r]
              /\ "pending" \in DOMAIN steps[r] /\ "expect" \in DOMAIN steps[r]
              /\ "ev" \in DOMAIN steps[r]
            BY DEF Shaped, StepDom
        <2>2. SUFFICES ASSUME steps' = [steps EXCEPT ![r].phase = "perform",
                                                     ![r].at = now,
                                                     ![r].pending = seq,
                                                     ![r].expect = docs[o]],
                              r \in DOMAIN steps,
                              "phase" \in DOMAIN steps[r],
                              "at" \in DOMAIN steps[r],
                              "pending" \in DOMAIN steps[r],
                              "expect" \in DOMAIN steps[r],
                              "ev" \in DOMAIN steps[r]
                       PROVE  /\ steps'[r].phase = "perform"
                              /\ steps'[r].at = now
                              /\ steps'[r].pending = seq
                              /\ steps'[r].expect = docs[o]
                              /\ steps'[r].ev = steps[r].ev
            BY <1>4, <2>1
        <2>3. QED
            BY <2>2, FourAt
    <1>6. steps'[r].at = now
        BY <1>5
    <1>7. steps'[r].expect = docs[o]
        BY <1>5
    <1>8. steps'[r].ev = steps[r].ev
        BY <1>5
    <1>9. steps'[r].pending = seq
        BY <1>5
    <1>10. DOMAIN steps' = DOMAIN steps
        BY <1>4, Zenon
    <1>11. \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
        BY <1>4, Zenon
    <1>12. seq \in Seq(Range(seq)) /\ Docs(seq, final, sends)
        <2>1. ASSUME NEW nn \in Nat, NEW mm \in Nat,
                     NEW pu, NEW de, NEW db, NEW sn,
                     NEW pr, NEW po, NEW rc, NEW sq,
                     /\ nn = Len(puts)
                     /\ mm = Len(dels)
                     /\ pu = puts
                     /\ de = dels
                     /\ db = final
                     /\ sn = sends
                     /\ pr = [i \in 1 .. nn |->
                                 [tag |-> "PutTimeout", entry |-> pu[i]]]
                     /\ po = [i \in 1 .. mm |->
                                 [tag |-> "DelTimeout", entry |-> de[i]]]
                     /\ rc = [tag |-> "PutDocument", body |-> db, sends |-> sn]
                     /\ sq = (pr \o <<rc>>) \o po
              PROVE  sq \in Seq(Range(sq)) /\ Docs(sq, db, sn)
            BY <2>1, OnlyDoc
        <2>2. QED
            BY <1>3, <2>1 DEF pre, post, rec, seq
    <1>13. st.at = now /\ st.expect = docs[o] /\ st.ev = steps[r].ev
           /\ st.pending = seq /\ st.phase = "perform"
        BY <1>5, <1>6, <1>7, <1>8, <1>9 DEF st
    <1>14. Sweep(st.expect, st.at) = swept
        BY <1>13 DEF swept, o
    <1>15. Handle(st.ev, swept.doc, st.at) = out
        BY <1>13, <1>14 DEF out
    <1>16. Image(st).doc = final /\ Image(st).sends = sends
        BY <1>14, <1>15, Isa DEF Image, final, sends
    <1>17. st.at \in 0 .. now'
        BY <1>1, <1>2, <1>6, SMT DEF st
    <1>18. Match(st, now')
        BY <1>12, <1>13, <1>16, <1>17, Zenon DEF Match
    <1>19. ASSUME NEW q \in DOMAIN steps'
           PROVE  steps'[q].phase = "perform" => Match(steps'[q], now')
        <2>1. q \in DOMAIN steps
            BY <1>10, <1>19
        <2>2. CASE q = r
            BY <1>13, <1>18, <2>2 DEF st
        <2>3. CASE q # r
            <3>1. steps'[q] = steps[q]
                BY <1>11, <2>1, <2>3
            <3>2. CASE steps[q].phase = "perform"
                <4>1. Match(steps[q], now)
                    BY <2>1, <3>2 DEF Queued
                <4>2. QED
                    BY <1>1, <3>1, <4>1, MatchSame
            <3>3. CASE steps[q].phase # "perform"
                BY <3>1, <3>3, Zenon
            <3>4. QED
                BY <3>2, <3>3
        <2>4. QED
            BY <2>2, <2>3
    <1>20. QED
        BY <1>2, <1>19 DEF Queued

LEMMA PendingAt ==
    ASSUME NEW r \in DOMAIN steps,
           NEW e,
           DOMAIN steps[r] = StepDom,
           steps' = [steps EXCEPT ![r].pending = e]
    PROVE  /\ steps'[r].pending = e
           /\ steps'[r].phase = steps[r].phase
           /\ steps'[r].at = steps[r].at
           /\ steps'[r].expect = steps[r].expect
           /\ steps'[r].ev = steps[r].ev
           /\ DOMAIN steps' = DOMAIN steps
           /\ DOMAIN steps'[r] = DOMAIN steps[r]
PROOF
    <1>1. "phase" \in DOMAIN steps[r] /\ "at" \in DOMAIN steps[r]
          /\ "pending" \in DOMAIN steps[r] /\ "expect" \in DOMAIN steps[r]
          /\ "ev" \in DOMAIN steps[r]
        BY DEF StepDom
    <1>2. ASSUME NEW ff, NEW xx, NEW gg, NEW ee,
                 /\ ff = steps
                 /\ xx = r
                 /\ gg = steps'
                 /\ ee = e
                 /\ xx \in DOMAIN ff
                 /\ "phase" \in DOMAIN ff[xx]
                 /\ "at" \in DOMAIN ff[xx]
                 /\ "pending" \in DOMAIN ff[xx]
                 /\ "expect" \in DOMAIN ff[xx]
                 /\ "ev" \in DOMAIN ff[xx]
                 /\ gg = [ff EXCEPT ![xx].pending = ee]
          PROVE  /\ gg[xx].pending = ee
                 /\ gg[xx].phase = ff[xx].phase
                 /\ gg[xx].at = ff[xx].at
                 /\ gg[xx].expect = ff[xx].expect
                 /\ gg[xx].ev = ff[xx].ev
                 /\ DOMAIN gg = DOMAIN ff
                 /\ DOMAIN gg[xx] = DOMAIN ff[xx]
        BY <1>2, OneAt
    <1>3. QED
        BY <1>1, <1>2

LEMMA ApplyPending ==
    ASSUME Shaped,
           NEW r \in DOMAIN steps,
           steps' = [steps EXCEPT ![r].pending = Tail(steps[r].pending)]
    PROVE  /\ steps'[r].pending = Tail(steps[r].pending)
           /\ steps'[r].ev = steps[r].ev
           /\ steps'[r].at = steps[r].at
           /\ steps'[r].expect = steps[r].expect
           /\ steps'[r].phase = steps[r].phase
PROOF
    <1>1. DOMAIN steps[r] = StepDom
        BY DEF Shaped
    <1>2. ASSUME NEW rr \in DOMAIN steps, NEW ee,
                 /\ rr = r
                 /\ ee = Tail(steps[r].pending)
                 /\ DOMAIN steps[rr] = StepDom
                 /\ steps' = [steps EXCEPT ![rr].pending = ee]
          PROVE  /\ steps'[rr].pending = ee
                 /\ steps'[rr].phase = steps[rr].phase
                 /\ steps'[rr].at = steps[rr].at
                 /\ steps'[rr].expect = steps[rr].expect
                 /\ steps'[rr].ev = steps[rr].ev
                 /\ DOMAIN steps' = DOMAIN steps
                 /\ DOMAIN steps'[rr] = DOMAIN steps[rr]
        BY <1>2, PendingAt
    <1>3. QED
        BY <1>1, <1>2

LEMMA ApplyMiss ==
    ASSUME Shaped,
           NEW r \in DOMAIN steps,
           steps' = [steps EXCEPT ![r].phase = "process",
                                  ![r].pending = << >>]
    PROVE  steps'[r].phase = "process"
PROOF
    <1>1. "phase" \in DOMAIN steps[r] /\ "at" \in DOMAIN steps[r]
          /\ "pending" \in DOMAIN steps[r] /\ "expect" \in DOMAIN steps[r]
          /\ "ev" \in DOMAIN steps[r]
        BY DEF Shaped, StepDom
    <1>2. SUFFICES ASSUME steps' = [steps EXCEPT ![r].phase = "process",
                                                 ![r].pending = << >>],
                          r \in DOMAIN steps,
                          "phase" \in DOMAIN steps[r],
                          "at" \in DOMAIN steps[r],
                          "pending" \in DOMAIN steps[r],
                          "expect" \in DOMAIN steps[r],
                          "ev" \in DOMAIN steps[r]
                   PROVE  steps'[r].phase = "process"
        BY <1>1
    <1>3. QED
        BY <1>2, MissAt

LEMMA ShapeKeep ==
    ASSUME Shaped,
           NEW r \in DOMAIN steps,
           DOMAIN steps' = DOMAIN steps,
           DOMAIN steps'[r] = StepDom,
           \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
    PROVE  Shaped'
PROOF
    <1>1. ASSUME NEW q \in DOMAIN steps'
          PROVE  DOMAIN steps'[q] = StepDom
        <2>1. q \in DOMAIN steps
            BY <1>1
        <2>2. CASE q = r
            BY <2>2
        <2>3. CASE q # r
            <3>1. steps'[q] = steps[q]
                BY <2>1, <2>3
            <3>2. QED
                BY <2>1, <3>1 DEF Shaped
        <2>4. QED
            BY <2>2, <2>3
    <1>2. QED
        BY <1>1 DEF Shaped

LEMMA TailShape ==
    ASSUME Shaped,
           NEW r \in DOMAIN steps,
           NEW e,
           steps' = [steps EXCEPT ![r].pending = e]
    PROVE  Shaped'
PROOF
    <1>1. DOMAIN steps[r] = StepDom
        BY DEF Shaped
    <1>2. ASSUME NEW rr \in DOMAIN steps, NEW ee,
                 /\ rr = r
                 /\ ee = e
                 /\ DOMAIN steps[rr] = StepDom
                 /\ steps' = [steps EXCEPT ![rr].pending = ee]
          PROVE  /\ steps'[rr].pending = ee
                 /\ steps'[rr].phase = steps[rr].phase
                 /\ steps'[rr].at = steps[rr].at
                 /\ steps'[rr].expect = steps[rr].expect
                 /\ steps'[rr].ev = steps[rr].ev
                 /\ DOMAIN steps' = DOMAIN steps
                 /\ DOMAIN steps'[rr] = DOMAIN steps[rr]
        BY <1>2, PendingAt
    <1>3. DOMAIN steps' = DOMAIN steps /\ DOMAIN steps'[r] = StepDom
        BY <1>1, <1>2
    <1>4. \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
        BY Zenon
    <1>5. QED
        BY <1>3, <1>4, ShapeKeep

LEMMA MissShape ==
    ASSUME Shaped,
           NEW r \in DOMAIN steps,
           steps' = [steps EXCEPT ![r].phase = "process",
                                  ![r].pending = << >>]
    PROVE  Shaped'
PROOF
    <1>1. "phase" \in DOMAIN steps[r] /\ "at" \in DOMAIN steps[r]
          /\ "pending" \in DOMAIN steps[r] /\ "expect" \in DOMAIN steps[r]
          /\ "ev" \in DOMAIN steps[r]
        BY DEF Shaped, StepDom
    <1>2. /\ steps'[r].phase = "process"
          /\ steps'[r].pending = << >>
          /\ DOMAIN steps' = DOMAIN steps
          /\ DOMAIN steps'[r] = DOMAIN steps[r]
        <2>1. SUFFICES ASSUME steps' = [steps EXCEPT ![r].phase = "process",
                                                     ![r].pending = << >>],
                              r \in DOMAIN steps,
                              "phase" \in DOMAIN steps[r],
                              "at" \in DOMAIN steps[r],
                              "pending" \in DOMAIN steps[r],
                              "expect" \in DOMAIN steps[r],
                              "ev" \in DOMAIN steps[r]
                       PROVE  /\ steps'[r].phase = "process"
                              /\ steps'[r].pending = << >>
                              /\ DOMAIN steps' = DOMAIN steps
                              /\ DOMAIN steps'[r] = DOMAIN steps[r]
            BY <1>1
        <2>2. QED
            BY <2>1, MissAt
    <1>3. DOMAIN steps'[r] = StepDom
        BY <1>2 DEF Shaped
    <1>4. \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
        BY Zenon
    <1>5. QED
        BY <1>2, <1>3, <1>4, ShapeKeep

LEMMA FourShape ==
    ASSUME Shaped,
           NEW r \in DOMAIN steps,
           NEW a, NEW b, NEW c, NEW d,
           steps' = [steps EXCEPT ![r].phase = a, ![r].at = b,
                                    ![r].pending = c, ![r].expect = d]
    PROVE  Shaped'
PROOF
    <1>1. "phase" \in DOMAIN steps[r] /\ "at" \in DOMAIN steps[r]
          /\ "pending" \in DOMAIN steps[r] /\ "expect" \in DOMAIN steps[r]
          /\ "ev" \in DOMAIN steps[r]
        BY DEF Shaped, StepDom
    <1>2. /\ steps'[r].phase = a
          /\ steps'[r].at = b
          /\ steps'[r].pending = c
          /\ steps'[r].expect = d
          /\ steps'[r].ev = steps[r].ev
          /\ DOMAIN steps' = DOMAIN steps
          /\ DOMAIN steps'[r] = DOMAIN steps[r]
        <2>1. SUFFICES ASSUME steps' = [steps EXCEPT ![r].phase = a, ![r].at = b,
                                                     ![r].pending = c, ![r].expect = d],
                              r \in DOMAIN steps,
                              "phase" \in DOMAIN steps[r],
                              "at" \in DOMAIN steps[r],
                              "pending" \in DOMAIN steps[r],
                              "expect" \in DOMAIN steps[r],
                              "ev" \in DOMAIN steps[r]
                       PROVE  /\ steps'[r].phase = a
                              /\ steps'[r].at = b
                              /\ steps'[r].pending = c
                              /\ steps'[r].expect = d
                              /\ steps'[r].ev = steps[r].ev
                              /\ DOMAIN steps' = DOMAIN steps
                              /\ DOMAIN steps'[r] = DOMAIN steps[r]
            BY <1>1
        <2>2. QED
            BY <2>1, FourAt
    <1>3. DOMAIN steps'[r] = StepDom
        BY <1>2 DEF Shaped
    <1>4. \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
        BY Zenon
    <1>5. QED
        BY <1>2, <1>3, <1>4, ShapeKeep

LEMMA ShapeAdd ==
    ASSUME Shaped,
           NEW r,
           NEW ev,
           r \notin DOMAIN steps,
           steps' = Set(steps, r, Fresh(ev))
    PROVE  Shaped'
PROOF
    <1>1. steps'[r] = Fresh(ev)
        BY Zenon DEF Set
    <1>2. DOMAIN steps' = (DOMAIN steps) \cup {r}
        BY Zenon DEF Set
    <1>3. DOMAIN Fresh(ev) = StepDom
        <2>1. ASSUME NEW ee, NEW pp, NEW xx, NEW tt, NEW rc,
                     /\ ee = ev
                     /\ pp = << >>
                     /\ xx = EmptyFn
                     /\ tt = NoTime
                     /\ rc = [ev |-> ee, phase |-> "process", pending |-> pp,
                              expect |-> xx, at |-> tt]
              PROVE  DOMAIN rc = {"ev", "phase", "pending", "expect", "at"}
                     /\ rc.phase = "process"
                     /\ rc.ev = ee
                     /\ rc.pending = pp
                     /\ rc.expect = xx
                     /\ rc.at = tt
            BY <2>1, DomRec
        <2>2. QED
            BY <2>1 DEF Fresh, EmptyFn, StepDom
    <1>4. DOMAIN steps'[r] = StepDom
        BY <1>1, <1>3
    <1>5. ASSUME NEW q \in DOMAIN steps'
          PROVE  DOMAIN steps'[q] = StepDom
        <2>1. CASE q = r
            BY <1>4, <2>1
        <2>2. CASE q # r
            <3>1. q \in DOMAIN steps /\ steps'[q] = steps[q]
                BY <1>2, <1>5, <2>2, Zenon DEF Set
            <3>2. QED
                BY <3>1 DEF Shaped
        <2>3. QED
            BY <2>1, <2>2
    <1>6. QED
        BY <1>5 DEF Shaped

LEMMA ShapeDrop ==
    ASSUME Shaped,
           NEW r \in DOMAIN steps,
           steps' = Del(steps, r)
    PROVE  Shaped'
PROOF
    <1>1. ASSUME NEW q \in DOMAIN steps'
          PROVE  q \in DOMAIN steps /\ q # r /\ steps'[q] = steps[q]
        BY <1>1, Zenon DEF Del
    <1>2. ASSUME NEW q \in DOMAIN steps'
          PROVE  DOMAIN steps'[q] = StepDom
        BY <1>1, <1>2 DEF Shaped
    <1>3. QED
        BY <1>2 DEF Shaped

LEMMA ShapeSame ==
    ASSUME Shaped, steps' = steps
    PROVE  Shaped'
PROOF
    BY Isa DEF Shaped

LEMMA ProcessShape ==
    ASSUME Shaped, NEW r \in DOMAIN steps, Process(r)
    PROVE  Shaped'
PROOF
    <1> DEFINE o == OriginOf(steps[r].ev)
               swept == Sweep(docs[o], now)
               out == Handle(steps[r].ev, swept.doc, now)
               final == out.doc
               puts == swept.puts \o out.puts
               dels == swept.dels \o out.dels
               sends == swept.sends \o out.sends
               pre == [n \in 1 .. Len(puts) |->
                          [tag |-> "PutTimeout", entry |-> puts[n]]]
               rec == [tag |-> "PutDocument", body |-> final, sends |-> sends]
               post == [n \in 1 .. Len(dels) |->
                           [tag |-> "DelTimeout", entry |-> dels[n]]]
               seq == (pre \o <<rec>>) \o post
    <1>1. steps' = [steps EXCEPT ![r].phase   = "perform",
                                ![r].at      = now,
                                ![r].pending = seq,
                                ![r].expect  = docs[o]]
        BY Isa DEF Process, o, swept, out, final, puts, dels, sends,
                            pre, rec, post, seq
    <1>2. ASSUME NEW rr \in DOMAIN steps, NEW aa, NEW bb, NEW cc, NEW dd,
                 /\ rr = r
                 /\ aa = "perform"
                 /\ bb = now
                 /\ cc = seq
                 /\ dd = docs[o]
                 /\ Shaped
                 /\ steps' = [steps EXCEPT ![rr].phase = aa, ![rr].at = bb,
                                            ![rr].pending = cc, ![rr].expect = dd]
          PROVE  Shaped'
        BY <1>2, FourShape
    <1>3. QED
        BY <1>1, <1>2 DEF o, seq

THEOREM QueueInit ==
    ASSUME Init
    PROVE  Queued
PROOF
    <1>1. now = 0
        BY DEF Init
    <1>2. now \in Nat
        BY <1>1, SMT
    <1>3. steps = << >>
        BY DEF Init, EmptyFn
    <1>4. << >> \in Seq(Nat) /\ Len(<< >>) = 0
        BY EmptySeq
    <1>5. DOMAIN steps = {}
        BY <1>3, <1>4, LenProperties
    <1>6. \A r \in DOMAIN steps :
            steps[r].phase = "perform" => Match(steps[r], now)
        BY <1>5
    <1>7. QED
        BY <1>2, <1>6 DEF Queued

THEOREM QueueStep ==
    ASSUME Queued, Shaped, [Next]_vars
    PROVE  Queued'
PROOF
    <1>1. ASSUME UNCHANGED vars
          PROVE  Queued'
        <2>1. now' = now /\ steps' = steps
            BY <1>1 DEF vars
        <2>2. QED
            BY <2>1, StutterKeeps
    <1>2. ASSUME NEW ev \in ExternalEvent, SubmitExternal(ev)
          PROVE  Queued'
        <2>1. PICK r \in Rid \ DOMAIN steps : steps' = Set(steps, r, Fresh(ev))
            BY <1>2 DEF SubmitExternal
        <2>2. now' = now /\ r \notin DOMAIN steps
            BY <1>2, <2>1 DEF SubmitExternal
        <2>3. QED
            BY <2>1, <2>2, AddKeeps
    <1>3. ASSUME NEW e \in timeouts, SubmitInternal(e)
          PROVE  Queued'
        <2>1. PICK r \in Rid \ DOMAIN steps :
                  steps' = Set(steps, r,
                               Fresh([tag |-> "Timeout", id |-> e.id, kind |-> e.kind]))
            BY <1>3 DEF SubmitInternal
        <2>2. now' = now /\ r \notin DOMAIN steps
            BY <1>3, <2>1 DEF SubmitInternal
        <2>3. QED
            BY <2>1, <2>2, AddKeeps
    <1>4. ASSUME NEW r \in DOMAIN steps, Process(r)
          PROVE  Queued'
        BY <1>4, ProcessKeeps
    <1>5. ASSUME NEW r \in DOMAIN steps, PerformDone(r)
          PROVE  Queued'
        <2>1. steps' = Del(steps, r) /\ now' = now
            BY <1>5 DEF PerformDone
        <2>2. QED
            BY <1>5, <2>1, DropKeeps
    <1>6. ASSUME NEW r \in DOMAIN steps, Crash(r)
          PROVE  Queued'
        <2>1. steps' = Del(steps, r) /\ now' = now
            BY <1>6 DEF Crash
        <2>2. QED
            BY <1>6, <2>1, DropKeeps
    <1>7. ASSUME Clock
          PROVE  Queued'
        <2>1. now' = now + 1 /\ steps' = steps
            BY <1>7 DEF Clock
        <2>2. QED
            BY <2>1, ClockKeeps
    <1>8. ASSUME NEW r \in DOMAIN steps, PerformPutTimeout(r)
          PROVE  Queued'
        <2>1. steps[r].phase = "perform" /\ steps[r].pending # << >> /\ now' = now
            BY <1>8 DEF PerformPutTimeout
        <2>2. steps' = [steps EXCEPT ![r].pending = Tail(steps[r].pending)]
            BY <1>8, Isa DEF PerformPutTimeout
        <2>3. DOMAIN steps' = DOMAIN steps
            BY <2>2, Zenon
        <2>4. steps'[r].pending = Tail(steps[r].pending)
              /\ steps'[r].ev = steps[r].ev /\ steps'[r].at = steps[r].at
              /\ steps'[r].expect = steps[r].expect
              /\ steps'[r].phase = steps[r].phase
            <3>1. ASSUME NEW rr \in DOMAIN steps,
                         /\ rr = r
                         /\ Shaped
                         /\ steps' = [steps EXCEPT ![rr].pending = Tail(steps[rr].pending)]
                  PROVE  /\ steps'[rr].pending = Tail(steps[rr].pending)
                         /\ steps'[rr].ev = steps[rr].ev
                         /\ steps'[rr].at = steps[rr].at
                         /\ steps'[rr].expect = steps[rr].expect
                         /\ steps'[rr].phase = steps[rr].phase
                BY <3>1, ApplyPending
            <3>2. QED
                BY <1>8, <2>2, <3>1
        <2>5. steps'[r].phase = "perform"
            BY <2>1, <2>4
        <2>6. \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
            BY <2>2, Zenon
        <2>7. QED
            BY <1>8, <2>1, <2>3, <2>4, <2>5, <2>6, TailKeeps
    <1>9. ASSUME NEW r \in DOMAIN steps, PerformPut(r)
          PROVE  Queued'
        <2>1. steps[r].phase = "perform" /\ steps[r].pending # << >> /\ now' = now
            BY <1>9 DEF PerformPut
        <2>2. steps' = [steps EXCEPT ![r].pending = Tail(steps[r].pending)]
            BY <1>9, Isa DEF PerformPut
        <2>3. DOMAIN steps' = DOMAIN steps
            BY <2>2, Zenon
        <2>4. steps'[r].pending = Tail(steps[r].pending)
              /\ steps'[r].ev = steps[r].ev /\ steps'[r].at = steps[r].at
              /\ steps'[r].expect = steps[r].expect
              /\ steps'[r].phase = steps[r].phase
            <3>1. ASSUME NEW rr \in DOMAIN steps,
                         /\ rr = r
                         /\ Shaped
                         /\ steps' = [steps EXCEPT ![rr].pending = Tail(steps[rr].pending)]
                  PROVE  /\ steps'[rr].pending = Tail(steps[rr].pending)
                         /\ steps'[rr].ev = steps[rr].ev
                         /\ steps'[rr].at = steps[rr].at
                         /\ steps'[rr].expect = steps[rr].expect
                         /\ steps'[rr].phase = steps[rr].phase
                BY <3>1, ApplyPending
            <3>2. QED
                BY <1>9, <2>2, <3>1
        <2>5. steps'[r].phase = "perform"
            BY <2>1, <2>4
        <2>6. \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
            BY <2>2, Zenon
        <2>7. QED
            BY <1>9, <2>1, <2>3, <2>4, <2>5, <2>6, TailKeeps
    <1>10. ASSUME NEW r \in DOMAIN steps, PerformDelTimeout(r)
           PROVE  Queued'
        <2>1. steps[r].phase = "perform" /\ steps[r].pending # << >> /\ now' = now
            BY <1>10 DEF PerformDelTimeout
        <2>2. steps' = [steps EXCEPT ![r].pending = Tail(steps[r].pending)]
            BY <1>10, Isa DEF PerformDelTimeout
        <2>3. DOMAIN steps' = DOMAIN steps
            BY <2>2, Zenon
        <2>4. steps'[r].pending = Tail(steps[r].pending)
              /\ steps'[r].ev = steps[r].ev /\ steps'[r].at = steps[r].at
              /\ steps'[r].expect = steps[r].expect
              /\ steps'[r].phase = steps[r].phase
            <3>1. ASSUME NEW rr \in DOMAIN steps,
                         /\ rr = r
                         /\ Shaped
                         /\ steps' = [steps EXCEPT ![rr].pending = Tail(steps[rr].pending)]
                  PROVE  /\ steps'[rr].pending = Tail(steps[rr].pending)
                         /\ steps'[rr].ev = steps[rr].ev
                         /\ steps'[rr].at = steps[rr].at
                         /\ steps'[rr].expect = steps[rr].expect
                         /\ steps'[rr].phase = steps[rr].phase
                BY <3>1, ApplyPending
            <3>2. QED
                BY <1>10, <2>2, <3>1
        <2>5. steps'[r].phase = "perform"
            BY <2>1, <2>4
        <2>6. \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
            BY <2>2, Zenon
        <2>7. QED
            BY <1>10, <2>1, <2>3, <2>4, <2>5, <2>6, TailKeeps
    <1>11. ASSUME NEW r \in DOMAIN steps, PerformMiss(r)
           PROVE  Queued'
        <2>1. now' = now
            BY <1>11 DEF PerformMiss
        <2>2. steps' = [steps EXCEPT ![r].phase = "process",
                                     ![r].pending = << >>]
            BY <1>11, Isa DEF PerformMiss
        <2>3. DOMAIN steps' = DOMAIN steps
            BY <2>2, Zenon
        <2>4. steps'[r].phase = "process"
            <3>1. ASSUME NEW rr \in DOMAIN steps,
                         /\ rr = r
                         /\ Shaped
                         /\ steps' = [steps EXCEPT ![rr].phase = "process",
                                                  ![rr].pending = << >>]
                  PROVE  steps'[rr].phase = "process"
                BY <3>1, ApplyMiss
            <3>2. QED
                BY <1>11, <2>2, <3>1
        <2>5. \A q \in DOMAIN steps : q # r => steps'[q] = steps[q]
            BY <2>2, Zenon
        <2>6. QED
            BY <1>11, <2>1, <2>3, <2>4, <2>5, MissKeeps
    <1>12. QED
        <2>1. CASE UNCHANGED vars
            BY <2>1, <1>1
        <2>2. CASE \E ev \in ExternalEvent : SubmitExternal(ev)
            <3>1. PICK ev \in ExternalEvent : SubmitExternal(ev)
                BY <2>2
            <3>2. QED
                BY <3>1, <1>2
        <2>3. CASE \E e \in timeouts : SubmitInternal(e)
            <3>1. PICK e \in timeouts : SubmitInternal(e)
                BY <2>3
            <3>2. QED
                BY <3>1, <1>3
        <2>4. CASE \E r \in DOMAIN steps : Process(r)
            <3>1. PICK r \in DOMAIN steps : Process(r)
                BY <2>4
            <3>2. QED
                BY <3>1, <1>4
        <2>5. CASE \E r \in DOMAIN steps : Crash(r)
            <3>1. PICK r \in DOMAIN steps : Crash(r)
                BY <2>5
            <3>2. QED
                BY <3>1, <1>6
        <2>6. CASE Clock
            BY <2>6, <1>7
        <2>7. CASE \E r \in DOMAIN steps : Perform(r)
            <3>1. PICK r \in DOMAIN steps : Perform(r)
                BY <2>7
            <3>2. CASE PerformDone(r)
                BY <3>1, <3>2, <1>5 DEF Perform
            <3>3. CASE PerformPutTimeout(r)
                BY <3>1, <3>3, <1>8 DEF Perform
            <3>4. CASE PerformDelTimeout(r)
                BY <3>1, <3>4, <1>10 DEF Perform
            <3>5. CASE PerformMiss(r)
                BY <3>1, <3>5, <1>11 DEF Perform
            <3>6. CASE PerformPut(r)
                BY <3>1, <3>6, <1>9 DEF Perform
            <3>7. QED
                BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Perform
        <2>8. QED
            BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next, vars

THEOREM ShapeInit ==
    ASSUME Init
    PROVE  Shaped
PROOF
    <1>1. steps = << >>
        BY DEF Init, EmptyFn
    <1>2. << >> \in Seq(Nat) /\ Len(<< >>) = 0
        BY EmptySeq
    <1>3. DOMAIN steps = {}
        BY <1>1, <1>2, LenProperties
    <1>4. QED
        BY <1>3 DEF Shaped

THEOREM ShapeStep ==
    ASSUME Shaped, [Next]_vars
    PROVE  Shaped'
PROOF
    <1>1. ASSUME UNCHANGED vars
          PROVE  Shaped'
        <2>1. steps' = steps
            BY <1>1 DEF vars
        <2>2. QED
            BY <2>1, ShapeSame
    <1>2. ASSUME NEW ev \in ExternalEvent, SubmitExternal(ev)
          PROVE  Shaped'
        <2>1. PICK r \in Rid \ DOMAIN steps : steps' = Set(steps, r, Fresh(ev))
            BY <1>2 DEF SubmitExternal
        <2>2. r \notin DOMAIN steps
            BY <2>1
        <2>3. QED
            BY <2>1, <2>2, ShapeAdd
    <1>3. ASSUME NEW e \in timeouts, SubmitInternal(e)
          PROVE  Shaped'
        <2>1. PICK r \in Rid \ DOMAIN steps :
                  steps' = Set(steps, r,
                               Fresh([tag |-> "Timeout", id |-> e.id, kind |-> e.kind]))
            BY <1>3 DEF SubmitInternal
        <2>2. r \notin DOMAIN steps
            BY <2>1
        <2>3. QED
            BY <2>1, <2>2, ShapeAdd
    <1>4. ASSUME NEW r \in DOMAIN steps, Process(r)
          PROVE  Shaped'
        BY <1>4, ProcessShape
    <1>5. ASSUME NEW r \in DOMAIN steps, PerformDone(r)
          PROVE  Shaped'
        <2>1. steps' = Del(steps, r)
            BY <1>5 DEF PerformDone
        <2>2. QED
            BY <1>5, <2>1, ShapeDrop
    <1>6. ASSUME NEW r \in DOMAIN steps, Crash(r)
          PROVE  Shaped'
        <2>1. steps' = Del(steps, r)
            BY <1>6 DEF Crash
        <2>2. QED
            BY <1>6, <2>1, ShapeDrop
    <1>7. ASSUME Clock
          PROVE  Shaped'
        <2>1. steps' = steps
            BY <1>7 DEF Clock
        <2>2. QED
            BY <2>1, ShapeSame
    <1>8. ASSUME NEW r \in DOMAIN steps, PerformPutTimeout(r)
          PROVE  Shaped'
        <2>1. steps' = [steps EXCEPT ![r].pending = Tail(steps[r].pending)]
            BY <1>8, Isa DEF PerformPutTimeout
        <2>2. ASSUME NEW rr \in DOMAIN steps, NEW ee,
                     /\ rr = r
                     /\ ee = Tail(steps[r].pending)
                     /\ Shaped
                     /\ steps' = [steps EXCEPT ![rr].pending = ee]
              PROVE  Shaped'
            BY <2>2, TailShape
        <2>3. QED
            BY <2>1, <2>2
    <1>9. ASSUME NEW r \in DOMAIN steps, PerformPut(r)
          PROVE  Shaped'
        <2>1. steps' = [steps EXCEPT ![r].pending = Tail(steps[r].pending)]
            BY <1>9, Isa DEF PerformPut
        <2>2. ASSUME NEW rr \in DOMAIN steps, NEW ee,
                     /\ rr = r
                     /\ ee = Tail(steps[r].pending)
                     /\ Shaped
                     /\ steps' = [steps EXCEPT ![rr].pending = ee]
              PROVE  Shaped'
            BY <2>2, TailShape
        <2>3. QED
            BY <2>1, <2>2
    <1>10. ASSUME NEW r \in DOMAIN steps, PerformDelTimeout(r)
           PROVE  Shaped'
        <2>1. steps' = [steps EXCEPT ![r].pending = Tail(steps[r].pending)]
            BY <1>10, Isa DEF PerformDelTimeout
        <2>2. ASSUME NEW rr \in DOMAIN steps, NEW ee,
                     /\ rr = r
                     /\ ee = Tail(steps[r].pending)
                     /\ Shaped
                     /\ steps' = [steps EXCEPT ![rr].pending = ee]
              PROVE  Shaped'
            BY <2>2, TailShape
        <2>3. QED
            BY <2>1, <2>2
    <1>11. ASSUME NEW r \in DOMAIN steps, PerformMiss(r)
           PROVE  Shaped'
        <2>1. steps' = [steps EXCEPT ![r].phase = "process",
                                     ![r].pending = << >>]
            BY <1>11, Isa DEF PerformMiss
        <2>2. ASSUME NEW rr \in DOMAIN steps,
                     /\ rr = r
                     /\ Shaped
                     /\ steps' = [steps EXCEPT ![rr].phase = "process",
                                              ![rr].pending = << >>]
              PROVE  Shaped'
            BY <2>2, MissShape
        <2>3. QED
            BY <2>1, <2>2
    <1>12. QED
        <2>1. CASE UNCHANGED vars
            BY <2>1, <1>1
        <2>2. CASE \E ev \in ExternalEvent : SubmitExternal(ev)
            <3>1. PICK ev \in ExternalEvent : SubmitExternal(ev)
                BY <2>2
            <3>2. QED
                BY <3>1, <1>2
        <2>3. CASE \E e \in timeouts : SubmitInternal(e)
            <3>1. PICK e \in timeouts : SubmitInternal(e)
                BY <2>3
            <3>2. QED
                BY <3>1, <1>3
        <2>4. CASE \E r \in DOMAIN steps : Process(r)
            <3>1. PICK r \in DOMAIN steps : Process(r)
                BY <2>4
            <3>2. QED
                BY <3>1, <1>4
        <2>5. CASE \E r \in DOMAIN steps : Crash(r)
            <3>1. PICK r \in DOMAIN steps : Crash(r)
                BY <2>5
            <3>2. QED
                BY <3>1, <1>6
        <2>6. CASE Clock
            BY <2>6, <1>7
        <2>7. CASE \E r \in DOMAIN steps : Perform(r)
            <3>1. PICK r \in DOMAIN steps : Perform(r)
                BY <2>7
            <3>2. CASE PerformDone(r)
                BY <3>1, <3>2, <1>5 DEF Perform
            <3>3. CASE PerformPutTimeout(r)
                BY <3>1, <3>3, <1>8 DEF Perform
            <3>4. CASE PerformDelTimeout(r)
                BY <3>1, <3>4, <1>10 DEF Perform
            <3>5. CASE PerformMiss(r)
                BY <3>1, <3>5, <1>11 DEF Perform
            <3>6. CASE PerformPut(r)
                BY <3>1, <3>6, <1>9 DEF Perform
            <3>7. QED
                BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Perform
        <2>8. QED
            BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next, vars

THEOREM InvInit ==
    ASSUME Init
    PROVE  Queued /\ Shaped
PROOF
    <1>1. Queued
        BY QueueInit
    <1>2. Shaped
        BY ShapeInit
    <1>3. QED
        BY <1>1, <1>2

THEOREM InvStep ==
    ASSUME Queued, Shaped, [Next]_vars
    PROVE  Queued' /\ Shaped'
PROOF
    <1>1. Queued'
        BY QueueStep
    <1>2. Shaped'
        BY ShapeStep
    <1>3. QED
        BY <1>1, <1>2

THEOREM QueueAlways ==
    Init /\ [][Next]_vars => [](Queued /\ Shaped)
PROOF
    <1>1. Init => Queued /\ Shaped
        BY InvInit
    <1>2. Queued /\ Shaped /\ [Next]_vars => Queued' /\ Shaped'
        BY InvStep
    <1>3. QED
        BY <1>1, <1>2, PTL

=============================================================================
