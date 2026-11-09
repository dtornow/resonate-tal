------------------------- MODULE DirectRefinement -------------------------
(***************************************************************************)
(* Claim boundary for the prototype.                                       *)
(*                                                                         *)
(*  1. SplitNetworkConcrete refines the atomic BatchedProtocol adapter.     *)
(*  2. Every adapter document step has an explicit finite DirectProtocol   *)
(*     expansion (B!BatchDocumentHasDirectExpansion).                       *)
(*                                                                         *)
(* The composition is trace expansion, not ordinary state refinement: the  *)
(* intermediate direct document states do not exist in a concrete run.     *)
(***************************************************************************)
EXTENDS SplitNetworkView

SplitConcreteRefinesBatch ==
    ConcreteSafety => BatchedSafety

BatchDocumentExpands ==
    B!BatchDocumentHasDirectExpansion

(* Named action obligation for a future all-symbolic TLAPS proof. Quiet
   executor actions stutter; a successful document CAS must be witnessed by
   B!ExpansionTraces at the recorded decision time. *)
SuccessfulPutHasExpansion ==
    \A r \in DOMAIN steps :
      PerformPutDocument(r) =>
        \E t \in 0 .. now :
          \E trace \in B!ExpansionTraces(t) :
            /\ trace[1] =
                 B!DocState(Objects, offers)
            /\ B!LastOf(trace) =
                 B!DocState(Objects', offers')
            /\ UNCHANGED <<network, now>>

THEOREM NetworkAndDocumentWritesAreSeparate ==
    Next => SeparatedWrites
PROOF
    BY NextSeparatesDocumentAndNetwork

=============================================================================
