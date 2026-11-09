# Direct-protocol refinement prototype

This prototype is additive. It does not change `Abstract.tla`, `Concrete.tla`,
or their existing refinement proof.

## Modules

- `DirectProtocol.tla` is the no-sweep protocol. One document transition
  performs one due item or one handler. A due item may add a message to the
  ghost `offers` set. `SendOffer` and `DropOffer` model an optional
  best-effort send; only `SendOffer` changes `network`.
- `BatchedProtocol.tla` is a trace-expansion adapter. A batched document
  transition is legal only when `ExpansionTraces(t)` contains a finite
  sequence of direct document transitions with the same endpoints.
- `SplitNetworkConcrete.tla` reuses the full-document sweep and executor
  operators from `Concrete` through an instance. Its successful CAS changes
  `docs` and publishes ghost offers. Separate send/drop actions change or
  discard those offers. `network` replaces `outbox` in the prototype.
- `SplitNetworkView.tla` supplies the document-flattening abstraction.
- `DirectRefinement.tla` states the concrete-to-batch temporal claim and the
  successful-CAS bridge obligation.

The intended theorem chain is:

```tla
SplitNetworkConcrete!Safety => BatchedProtocol!BSafety

BatchedProtocol!BatchedDocument
  => \E t, trace \in ExpansionTraces(t) :
       trace[1] = currentDocumentState
       /\ LastOf(trace) = nextDocumentState
       /\ every adjacent pair is a DirectProtocol document step
```

The second condition is enforced by the definition of `BatchedDocument` and
exposed as `BatchDocumentHasDirectExpansion`. The first claim is executable
with TLC:

```sh
java -cp tla2tools.jar tlc2.TLC \
  -config DirectRefinement.cfg -deadlock DirectRefinement.tla
```

The small model enables create, settle, listener registration, and timeout.
It exercises full promise, retry, and listener sweeps plus offer publication,
network send, and network drop rather than checking only empty sweeps.
`DirectRefinementTasks.cfg` separately covers task create/release, including
lease expiry and retry. The checked graphs at this commit are complete:
39,231 distinct states for the promise/listener group and 1,852 for the task
group.

## Why this is trace expansion

Ordinary TLA+ refinement maps each concrete state to one abstract state and
allows a concrete transition to match one abstract transition or stuttering.
A successful concrete CAS can settle several deadlines, drain callbacks and
listeners, rearm retries, and run one handler atomically. The direct protocol
exposes those as several transitions, whose intermediate states have no
corresponding concrete states. No state-only refinement mapping can invent
them.

`BatchedProtocol` makes that mismatch explicit instead of weakening the
direct protocol: an atomic adapter step carries the finite direct trace that
must be inserted when expanding the concrete trace.

## Remaining proof obligations

1. Prove `SuccessfulPutHasExpansion` symbolically for every event and full
   alphabet. Existing `refinement_proof/SweepProof.tla` and the sweep/handler
   bridge establish most of the analogous old-outbox result, but are tightly
   coupled to `Abstract!Swept` and need a lemma converting the concrete send
   sequence into the `offers` endpoint of an `ExpansionTrace`.
2. Lift that action lemma, plus stuttering cases, to
   `SplitConcreteRefinesBatch` in TLAPS.
   TLAPS 1.5 does not finish elaborating `BatchedProtocol.tla`'s bounded set
   of sequence witnesses (even with no backend verification); SANY and TLC do.
   A TLAPS proof therefore also needs a less evaluator-heavy inductive trace
   representation or small bridge lemmas in a separate module.
3. If a conventional temporal refinement theorem directly to
   `DirectProtocol!Safety` is required, instrument the concrete machine with a
   replay phase and expose the replay states. That changes the observed state
   cadence; without such instrumentation the theorem is false in the standard
   state-refinement sense.
4. Liveness is intentionally absent. Best-effort offers can be retained or
   dropped, and crashes can continue forever. Any delivery theorem needs an
   explicit fairness/reliability premise.
