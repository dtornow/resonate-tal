# Refinement proof

These modules prove the refinement claim in `../refinement_claim/Refinement.tla`.

Run the final TLAPS proof from `spec/tlap`:

```sh
/home/ubuntu/tlaps/bin/tlapm --threads 1 \
  -I refinement_claim -I refinement_proof \
  refinement_proof/Proof.tla
```
