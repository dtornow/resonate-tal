------------------------------ MODULE Refinement ------------------------------
(* DOES THE EXECUTOR IMPLEMENT THE PROTOCOL?

   The clock is the same clock. It ticks by itself, and a write leaves it
   alone. The write stores the time the decision was made, which is at most
   that clock. The compare-and-swap is the only coordination. The document
   and the outbox are the protocol's own. *)
EXTENDS ConcreteView

(* Temporary target for the established one-step proof. The replacement
   claim targets direct Abstract through the trace-expansion adapter. *)
P == INSTANCE SweptAbstract WITH objects <- Objects

(* Named entry points for TLC; the TLAPS theorem states the implication
   directly instead of hiding either side behind these names. *)
ConcreteBehavior ==
    Init /\ [][Next]_vars

AbstractSafety ==
    P!Safety

===============================================================================
