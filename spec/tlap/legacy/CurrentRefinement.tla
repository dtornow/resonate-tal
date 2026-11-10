------------------------ MODULE CurrentRefinement ------------------------
(* Executable check of the current models, without a batching adapter. *)
EXTENDS Concrete

Objects ==
    [ id \in UNION { DOMAIN docs[o] : o \in Origin }
      |-> docs[id.origin][id] ]

A ==
    INSTANCE Abstract
        WITH objects <- Objects,
             network <- outbox

Refines ==
    A!Spec

=============================================================================
