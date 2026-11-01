------------------------------ MODULE Refinement ------------------------------
(* DOES THE EXECUTOR IMPLEMENT THE PROTOCOL?

   The clock is the same clock. It ticks by itself, and a write leaves it
   alone. The write stores the time the decision was made, which is at most
   that clock. The compare-and-swap is the only coordination. The document
   and the outbox are the protocol's own. *)
EXTENDS Concrete

P == INSTANCE Abstract WITH objects <- Objects

SpecR ==
    Init /\ [][Next]_vars

Refines ==
    P!Safety

===============================================================================
