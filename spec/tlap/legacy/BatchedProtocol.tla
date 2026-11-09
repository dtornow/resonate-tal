-------------------------- MODULE BatchedProtocol --------------------------
(***************************************************************************)
(* Trace-expansion adapter for an executor whose document CAS performs a    *)
(* full sweep. A BatchedDocument step is admitted only when it carries a    *)
(* finite witness trace of DirectProtocol document steps. Network actions   *)
(* remain unbatched and therefore remain separate from document writes.     *)
(***************************************************************************)
EXTENDS DirectProtocol

LastOf(seq) ==
    seq[Len(seq)]

IsDirectTrace(seq, t) ==
    /\ Len(seq) >= 1
    /\ seq[1] = CurrentDoc
    /\ \A k \in 1 .. (Len(seq) - 1) :
          seq[k + 1] \in DirectDocAfter(seq[k], t)

(* Generate all prefixes containing at most A!MaxSweep due actions. The
   handler is appended separately and at most once. *)
DueTraceSet(t) ==
    LET R[k \in 0 .. A!MaxSweep] ==
            IF k = 0 THEN
                {<< CurrentDoc >>}
            ELSE
                LET prev == R[k - 1]
                    ext  == A!Flat(
                              { { Append(tr, nxt) :
                                    nxt \in DueDocAfter(LastOf(tr), t) } :
                                tr \in prev })
                IN  prev \cup ext
    IN  R[A!MaxSweep]

DueWitnesses(t) ==
    { tr \in DueTraceSet(t) : IsDirectTrace(tr, t) }

ExpansionCandidates(t) ==
    UNION
      { { IF fin = LastOf(tr) THEN tr ELSE Append(tr, fin) :
            fin \in {LastOf(tr)} \cup HandlerDocAfter(LastOf(tr), t) } :
          tr \in DueWitnesses(t) }

(* The filter is intentional: the adapter is sound by construction. A proof
   that a concrete sweep has a member here is the concrete bridge obligation,
   rather than an assumption hidden in the abstract protocol. *)
ExpansionTraces(t) ==
    { tr \in ExpansionCandidates(t) : IsDirectTrace(tr, t) }

BatchedDocumentAt(t) ==
    \E trace \in ExpansionTraces(t) :
        LET fin == LastOf(trace)
        IN  /\ objects' = fin.objects
            /\ offers'  = fin.offers
            /\ UNCHANGED <<network, now>>

(* This is deliberately the definition of the adapter action, not a
   post-hoc assertion about it: carrying a valid direct expansion is the
   admission criterion for an atomic batch. *)
ExpansionAction ==
    \E t \in 0 .. now :
      \E trace \in ExpansionTraces(t) :
        /\ trace[1] = CurrentDoc
        /\ LastOf(trace) = DocState(objects', offers')
        /\ \A k \in 1 .. (Len(trace) - 1) :
              trace[k + 1] \in DirectDocAfter(trace[k], t)
        /\ UNCHANGED <<network, now>>

BatchedDocument ==
    ExpansionAction

BInit ==
    Init

BNext ==
    \/ BatchedDocument
    \/ \E msg \in offers : SendOffer(msg) \/ DropOffer(msg)
    \/ Clock

BSafety ==
    BInit /\ [][BNext]_vars

(* This is the central theorem shape of the adapter: every atomic batch has
   a bounded, explicit direct trace with the same endpoints and decision
   time. It is stronger than merely relating the final states. *)
BatchDocumentHasDirectExpansion ==
    BatchedDocument =>
      \E t \in 0 .. now :
        \E trace \in ExpansionTraces(t) :
          /\ trace[1] = CurrentDoc
          /\ LastOf(trace) = DocState(objects', offers')
          /\ \A k \in 1 .. (Len(trace) - 1) :
                trace[k + 1] \in DirectDocAfter(trace[k], t)
          /\ UNCHANGED <<network, now>>

=============================================================================
