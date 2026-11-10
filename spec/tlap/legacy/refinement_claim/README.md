# Refinement claim

`Refinement.tla` states the abstraction from the concrete executor to the
abstract protocol. The proof states the claim directly:

```tla
Init /\ [][Next]_vars => P!Safety
```

`ConcreteBehavior` and `AbstractSafety` are only named TLC configuration
entry points.
