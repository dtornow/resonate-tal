--------------------------- MODULE ConcreteView ---------------------------
(* Refinement and checker view of the concrete executor. Concrete itself
   has no dependency on the abstract protocol. *)
EXTENDS Concrete

Objects ==
    [ i \in UNION { DOMAIN docs[o] : o \in Origin }
      |-> docs[i.origin][i] ]

A ==
    INSTANCE SweptAbstract WITH objects <- Objects

C_UnitCoherent ==
    A!UnitCoherent

CT_preserved_settled_promise_record ==
    [][A!preserved_settled_promise_record]_vars

CT_consistent_promise_settlement_stamp ==
    [][A!consistent_promise_settlement_stamp]_vars

=============================================================================
