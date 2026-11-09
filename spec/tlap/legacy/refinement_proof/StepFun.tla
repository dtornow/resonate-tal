----------------------------- MODULE StepFun -----------------------------
(* Field updates of a step record are function overrides. Zenon reads a
   field off EXCEPT once that field is in the record domain, and an
   override leaves the domain and the other fields alone. *)
EXTENDS TLAPS

LEMMA OneAt ==
    ASSUME NEW f, NEW x, NEW g, NEW e,
           x \in DOMAIN f,
           "phase" \in DOMAIN f[x],
           "at" \in DOMAIN f[x],
           "pending" \in DOMAIN f[x],
           "expect" \in DOMAIN f[x],
           "ev" \in DOMAIN f[x],
           g = [f EXCEPT ![x].pending = e]
    PROVE  /\ g[x].pending = e
           /\ g[x].phase = f[x].phase
           /\ g[x].at = f[x].at
           /\ g[x].expect = f[x].expect
           /\ g[x].ev = f[x].ev
           /\ DOMAIN g = DOMAIN f
           /\ DOMAIN g[x] = DOMAIN f[x]
PROOF BY Zenon

LEMMA MissAt ==
    ASSUME NEW f, NEW x, NEW g, NEW a, NEW e,
           x \in DOMAIN f,
           "phase" \in DOMAIN f[x],
           "at" \in DOMAIN f[x],
           "pending" \in DOMAIN f[x],
           "expect" \in DOMAIN f[x],
           "ev" \in DOMAIN f[x],
           g = [f EXCEPT ![x].phase = a, ![x].pending = e]
    PROVE  /\ g[x].phase = a
           /\ g[x].pending = e
           /\ g[x].at = f[x].at
           /\ g[x].expect = f[x].expect
           /\ g[x].ev = f[x].ev
           /\ DOMAIN g = DOMAIN f
           /\ DOMAIN g[x] = DOMAIN f[x]
PROOF BY Zenon

LEMMA FourAt ==
    ASSUME NEW f, NEW x, NEW g, NEW a, NEW b, NEW c, NEW d,
           x \in DOMAIN f,
           "phase" \in DOMAIN f[x],
           "at" \in DOMAIN f[x],
           "pending" \in DOMAIN f[x],
           "expect" \in DOMAIN f[x],
           "ev" \in DOMAIN f[x],
           g = [f EXCEPT ![x].phase = a, ![x].at = b,
                         ![x].pending = c, ![x].expect = d]
    PROVE  /\ g[x].phase = a
           /\ g[x].at = b
           /\ g[x].pending = c
           /\ g[x].expect = d
           /\ g[x].ev = f[x].ev
           /\ DOMAIN g = DOMAIN f
           /\ DOMAIN g[x] = DOMAIN f[x]
PROOF BY Zenon

LEMMA DomRec ==
    ASSUME NEW ev, NEW pend, NEW exp, NEW tm, NEW rec,
           rec = [ev |-> ev, phase |-> "process", pending |-> pend,
                  expect |-> exp, at |-> tm]
    PROVE  DOMAIN rec = {"ev", "phase", "pending", "expect", "at"}
            /\ rec.phase = "process"
            /\ rec.ev = ev
            /\ rec.pending = pend
            /\ rec.expect = exp
            /\ rec.at = tm
PROOF BY Zenon

====
