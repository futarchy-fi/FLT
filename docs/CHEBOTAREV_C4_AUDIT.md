# C4: Frobenius-trace criterion audit

Checked at 2026-09-27 15:59 UTC for implementation commit
`fd8c875d6d6883411c930a6bd6ed6dd6f106289a`.

`GaloisRepresentation.B5Inputs.not_isIrreducible_of_frobenius_traces`
now applies `powerFrobCover_of_finite` and `trace_identity_of_powerFrobCover`
with `N = p + 1`. The determinant hypothesis and
`cyclotomicCharacter_adicArithFrob` give the trace identity on the chosen
Frobenius elements. C3 transports its equivalent fixed-vector property
through powers and conjugation, and the existing rank-two criterion concludes.

The theorem's signature is byte-for-byte unchanged. Its Frobenius section,
including the cyclotomic formula and the two proved special-case/reduction
lemmas, moved from `B5Inputs.lean` to `Chebotarev/FrobeniusTraces.lean`.
B5Inputs re-exports this module, so PrimeField's source and imports are unchanged.
`FLT.lean` has the new public import in C-locale order.

The unused admitted declaration `chebotarev_frobenius_dense` was removed.
No Lean source still references it. This removes the stronger theorem from B5;
it does not establish full Chebotarev density.

## Reproduce the checks

```bash
LEAN_NUM_THREADS=4 lake build FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FrobeniusTraces
LEAN_NUM_THREADS=4 lake build
# Expected: no exact-name matches (exit 1).
rg -n 'chebotarev_frobenius_dense\b' FLT --glob '*.lean'
```

Save the following as `/tmp/c4-audit.lean`, then run
`LEAN_NUM_THREADS=4 lake env lean /tmp/c4-audit.lean`:

```lean
import FLT.GaloisRepresentation.HardlyRamified.PrimeField
import Mathlib.Util.PrintSorries

#print axioms GaloisRepresentation.B5Inputs.chebotarev_frobenius_dense_of_surjective_group_case
#print axioms GaloisRepresentation.B5Inputs.cyclotomicCharacter_adicArithFrob
#print axioms GaloisRepresentation.B5Inputs.modularCyclotomicCharacter_adicArithFrob
#print axioms GaloisRepresentation.B5Inputs.chebotarev_frobenius_dense_of_factors_cyclotomic
#print axioms GaloisRepresentation.B5Inputs.powerFrobCover_of_finite
#print axioms GaloisRepresentation.B5Inputs.trace_identity_of_powerFrobCover
#print axioms GaloisRepresentation.B5Inputs.not_isIrreducible_of_frobenius_traces
#print axioms GaloisRepresentation.IsHardlyRamified.not_isIrreducible_of_prime_field
#print sorries GaloisRepresentation.IsHardlyRamified.not_isIrreducible_of_prime_field
```

## Results

The seven B5Inputs declarations printed exactly
`[propext, Classical.choice, Quot.sound]`; none depends on `sorryAx`.
The prime-field caller printed `[propext, sorryAx, Classical.choice, Quot.sound]`.
Mathlib's `#print sorries` traced that remaining admission dependency to exactly:

- `GaloisRepresentation.IsHardlyRamified.lifts`
- `GaloisRepresentation.IsHardlyRamified.mem_isCompatible`
- `GaloisRepresentation.IsHardlyRamified.three_adic`

These existing admissions were not changed. The axiom and admission-tracing
commands exited 0; the module build passed (4225 jobs), and the full
`lake build` passed (9554 jobs, including `FermatsLastTheorem`).
Full build output: `/tmp/c4-full-build.log`. No full `lake lint` ran.
The original check files and outputs are `/tmp/c4-axioms.lean`,
`/tmp/c4-axioms.log`, `/tmp/c4-remaining-sorries.lean`, and
`/tmp/c4-remaining-sorries.log` on General.

The same proof result is recorded in the local hub memory commit `ac0995da`,
`log/2026-09-27-chebotarev-c4.md`; neither repository was pushed.
