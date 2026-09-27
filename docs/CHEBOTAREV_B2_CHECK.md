# Chebotarev B2 verification

Implementation: `FLT/GaloisRepresentation/HardlyRamified/Chebotarev/PrimeFibers.lean`.
All declarations below are in `GaloisRepresentation.Chebotarev`.

The requested `sum_norm_powers_over_unramified` has the plan's signature, using
`v.asIdeal.absNorm` for its proposed `norm v`. Its unused unramified hypothesis
is named `_hu`: the stronger `sum_norm_powers_over` also applies to ramified
primes. The finite fiber instance is already supplied by Mathlib.

The supporting results prove constant norms in each Galois fiber, the
unramified identity `card * inertiaDegIn = finrank`, the split-prime
contribution, and residue degree at least two when Frobenius is nontrivial.
They reuse B1's definitions and proofs. Existing admissions are unchanged.

Checked at 2026-09-27 14:54 UTC with:

```sh
LEAN_NUM_THREADS=4 lake build FLT.GaloisRepresentation.HardlyRamified.Chebotarev.PrimeFibers
```

Result: success (3603 jobs), no warnings from the new module.

For a reproducible axiom audit, save the following to a temporary Lean file and
run `LEAN_NUM_THREADS=4 lake env lean /tmp/chebotarev-b2-axioms.lean`:

```lean
import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.PrimeFibers
#print axioms GaloisRepresentation.Chebotarev.absNorm_eq_pow_inertiaDegIn
#print axioms GaloisRepresentation.Chebotarev.sum_norm_powers_over
#print axioms GaloisRepresentation.Chebotarev.sum_norm_powers_over_unramified
#print axioms GaloisRepresentation.Chebotarev.card_primesOver_mul_inertiaDegIn
#print axioms GaloisRepresentation.Chebotarev.inertiaDegIn_eq_one_of_frob_eq_one
#print axioms GaloisRepresentation.Chebotarev.sum_norm_powers_over_split
#print axioms GaloisRepresentation.Chebotarev.two_le_inertiaDegIn_of_frob_ne_one
```

Checked at 2026-09-27 14:54 UTC; exit 0. Each command printed exactly the axiom
set `[propext, Classical.choice, Quot.sound]`; none depends on `sorryAx` or a
new axiom.

Full repository check, completed at 2026-09-27 14:59 UTC:

```sh
LEAN_NUM_THREADS=4 lake build
```

Result: exit 0, `Build completed successfully (9531 jobs).`
`git diff --check` also passed. No full `lake lint` was run, as directed by the brief.
