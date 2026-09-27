# D1: higher-degree prime sums

Implementation: `FLT/GaloisRepresentation/HardlyRamified/Chebotarev/HigherDegree.lean`.
Source commit: `2b5f148d`. All declarations below are in `GaloisRepresentation.Chebotarev`.

`HigherDegree` and `higherDegree_primeSum_bounded` have the statements in
`CHEBOTAREV_PLAN.md`, with the field, number-field, and algebra instances explicit.
The extension need not be Galois. The proof reuses D2's `Prime`, `norm`, and `ps`
and Z2's `Chebotarev.summable_primeNorm`.

The auxiliary bound uses `Module.finrank (𝓞 K) (𝓞 L)` as its constant.
Mathlib's ramification–inertia sum bounds each fiber by this rank directly;
identifying it with the field degree is unnecessary for boundedness.
The proof establishes summability before comparing or reindexing infinite sums.

Reproduce the build and trust checks:

```sh
LEAN_NUM_THREADS=4 lake build FLT.GaloisRepresentation.HardlyRamified.Chebotarev.HigherDegree
LEAN_NUM_THREADS=4 lake build
cat > /tmp/chebotarev-d1-axioms.lean <<'LEAN'
import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.HigherDegree
#print axioms GaloisRepresentation.Chebotarev.card_primesOver_le
#print axioms GaloisRepresentation.Chebotarev.norm_rpow_le_of_inertiaDeg_ge_two
#print axioms GaloisRepresentation.Chebotarev.higherDegree_primeSum_le
#print axioms GaloisRepresentation.Chebotarev.higherDegree_primeSum_bounded
LEAN
LEAN_NUM_THREADS=4 lake env lean /tmp/chebotarev-d1-axioms.lean
```

Axiom checks passed on 2026-09-27 at 14:54 UTC. Each of the four theorems uses
exactly `[propext, Classical.choice, Quot.sound]`; none depends on `sorryAx`.
The module build passed without warnings. The full `LEAN_NUM_THREADS=4 lake build`
passed on 2026-09-27 at 14:59 UTC: `Build completed successfully (9534 jobs).`
`git diff --check` passed, and the public imports in `FLT.lean` are sorted
in `LC_ALL=C` order. Existing admissions were not modified.
