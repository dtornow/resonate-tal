# resonate-tal

TLA+ models copied from [resonatehq/resonate](https://github.com/resonatehq/resonate) [`spec/tlap`](https://github.com/resonatehq/resonate/tree/9c72d818721b1776edd6b1b2939a83b3c0b248a6/spec/tlap) at `9c72d818721b1776edd6b1b2939a83b3c0b248a6` (`main`). The directory was last changed in `9cde480c38` (“Drop address validation from the specification”, 29 Aug 2026).

| | |
|---|---|
| `spec/tlap/Abstract.tla` | the protocol: one direct timeout, callback, listener, request, or clock action per step |
| `spec/tlap/Concrete.tla` | the same protocol as one document per origin, with a CAS and a timeout wheel |
| `spec/tlap/Requests.tla` | shared protocol vocabulary |
| `spec/tlap/legacy/` | swept adapter, refinement proofs, checkers, and experiments |

See `spec/tlap/README.md` for active model checks and the legacy proof archive.
