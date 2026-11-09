# Refinement proof

These archived modules prove the swept-adapter claim in
`../refinement_claim/Refinement.tla`.

Run the final TLAPS proof from `spec/tlap`:

```sh
/home/ubuntu/tlaps/bin/tlapm --threads 1 \
  -I . -I legacy -I legacy/refinement_claim -I legacy/refinement_proof \
  legacy/refinement_proof/Proof.tla
```
