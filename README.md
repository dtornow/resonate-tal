# resonate-tal

TLA+ models copied from [resonatehq/resonate](https://github.com/resonatehq/resonate) [`spec/tlap`](https://github.com/resonatehq/resonate/tree/9c72d818721b1776edd6b1b2939a83b3c0b248a6/spec/tlap) at `9c72d818721b1776edd6b1b2939a83b3c0b248a6` (`main`). The directory was last changed in `9cde480c38` (“Drop address validation from the specification”, 29 Aug 2026).

| | |
|---|---|
| `spec/tlap/Abstract.tla` | the protocol: a step may sweep any number of due actions, then one request |
| `spec/tlap/Concrete.tla` | the same protocol as one document per origin, with a CAS and a timeout wheel |

`Requests.tla` is the shared vocabulary. `Invariants.tla` is the catalogue, instantiated by both machines. Configs, `check.sh`, and the checker generators sit beside the modules. See `spec/tlap/README.md`.
