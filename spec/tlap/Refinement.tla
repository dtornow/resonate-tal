------------------------------ MODULE Refinement ------------------------------
(* DOES THE EXECUTOR IMPLEMENT THE PROTOCOL?

   One abstract step takes any number of due actions, then a handler, and
   may move the clock forward. One concrete write does that work in one go,
   at the instant Process read the clock, and lands it later.

   The abstract clock is the oldest `at` among writes that can still land.
   It is computed from `steps`, not stored. While that write is in flight a
   tick of the concrete clock leaves it where it is. The write is the
   abstract step: the document and the outbox land together, and the clock
   moves on to the next oldest decision, or to the concrete clock when none
   remain. *)
EXTENDS Concrete

(* A write that can still land: the step has reached its document write, and
   the document is still the one Process decided against. *)
Holders ==
    { r \in DOMAIN steps :
        /\ steps[r].phase = "perform"
        /\ \E n \in DOMAIN steps[r].pending :
               steps[r].pending[n].tag = "PutDocument"
        /\ docs[OriginOf(steps[r].ev)] = steps[r].expect }

AbstractNow ==
    LET times == { steps[r].at : r \in Holders }
    IN  IF times = {} THEN now
        ELSE CHOOSE t \in times : \A u \in times : t <= u

P == INSTANCE Abstract WITH
         objects <- Objects,
         now     <- AbstractNow

SpecR ==
    Init /\ [][Next]_vars

Refines ==
    P!Safety

===============================================================================
