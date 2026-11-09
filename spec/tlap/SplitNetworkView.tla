------------------------- MODULE SplitNetworkView -------------------------
(* Refinement view for SplitNetworkConcrete. *)
EXTENDS SplitNetworkConcrete

Objects ==
    [ i \in UNION { DOMAIN docs[o] : o \in Origin }
      |-> docs[i.origin][i] ]

B ==
    INSTANCE BatchedProtocol WITH objects <- Objects

ConcreteSafety ==
    Init /\ [][Next]_vars

BatchedSafety ==
    B!BSafety

AbsVars ==
    <<Objects, offers, network, now>>

=============================================================================
