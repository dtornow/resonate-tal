# Legacy and proof material

This directory contains the swept abstract adapter, refinement proofs,
generated checker modules, experimental trace-expansion models, and their
supporting configurations.

`AbstractBatch.tla` is the declarative batch adapter: six fixed stages choose
any eligible subset without recursive sweep closure or `MaxSweep`.

The active model is intentionally small:

- `../Requests.tla`
- `../Abstract.tla`
- `../Concrete.tla`
