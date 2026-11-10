# Legacy and proof material

This directory contains the swept abstract adapter, refinement proofs,
generated checker modules, experimental trace-expansion models, and their
supporting configurations.

`AbstractBatch.tla` is the declarative batch adapter: six fixed stages choose
any eligible subset without recursive sweep closure or `MaxSweep`.

`CurrentRefinement.tla` is the exact executable check:

```tla
Concrete!Spec => Abstract!Spec
```

It currently fails on the frozen-decision-time counterexample documented by
TLC: Concrete prepares at time 0, ticks to 1, then commits the time-0 body.

The active model is intentionally small:

- `../Requests.tla`
- `../Abstract.tla`
- `../Concrete.tla`
