# D2: negligible sets and large norms

Implementation: `FLT/GaloisRepresentation/HardlyRamified/Chebotarev/NegligibleSets.lean`.
All declarations are in `GaloisRepresentation.Chebotarev`.

The definitions `Prime`, `norm`, `ell`, `ps`, and `LogDensity` follow
`CHEBOTAREV_PLAN.md`. In particular, `LogDensity` uses `log (1 / (s - 1))`,
not Mathlib's sum over all prime ideals.

`logDensity_diff` has one additional leading hypothesis:

```lean
(hsum : ∀ s : ℝ, 1 < s → Summable (fun v : Prime K ↦ (norm v : ℝ) ^ (-s)))
```

This is precisely the Z2 input, which is not present on this branch. The brief
allows unavailable dependencies as explicit hypotheses. The proof bounds the
sum over `T ∩ U` by the sum over `U`, shows its normalized limit is zero, and
subtracts it from the sum over `T`. Every sum decomposition uses `hsum`.

`exists_norm_ge_of_logDensity_pos` has the planned signature with no added
hypothesis. If no requested prime exists, `T` is contained in the union of
`S` and the finite set of prime ideals of norm at most `N`. Its density is
therefore zero, contradicting `0 < d`. This also handles `N = 0`.

## Axiom check

Checked 2026-09-27 14:42 UTC with `lake env lean /tmp/d2-axioms.lean`.
Each command below reports exactly `[propext, Classical.choice, Quot.sound]`;
none reports `sorryAx` or a new axiom.

```lean
import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.NegligibleSets
#print axioms GaloisRepresentation.Chebotarev.tendsto_ell_atTop
#print axioms GaloisRepresentation.Chebotarev.tendsto_div_ell_of_isBigO
#print axioms GaloisRepresentation.Chebotarev.primeSum_isBigO_of_finite
#print axioms GaloisRepresentation.Chebotarev.logDensity_zero_of_finite
#print axioms GaloisRepresentation.Chebotarev.logDensity_diff
#print axioms GaloisRepresentation.Chebotarev.exists_norm_ge_of_logDensity_pos
```

Both builds passed, checked 2026-09-27 14:47 UTC. The full build
completed 9,529 jobs. Reproduce with:

```sh
LEAN_NUM_THREADS=4 lake build FLT.GaloisRepresentation.HardlyRamified.Chebotarev.NegligibleSets
LEAN_NUM_THREADS=4 lake build
```

Existing admissions are unchanged. D2 alone does not discharge Chebotarev or B5.
