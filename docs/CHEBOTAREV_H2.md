# H2: Frobenius membership and fixed-field splitting

Implementation: `FLT/GaloisRepresentation/HardlyRamified/Chebotarev/SubfieldSplitting.lean`.

`frob_mem_iff_split_fixedField` has the cyclic-extension statement from the plan,
including the hypothesis that the prime is unramified in the top field.
`frob_mem_iff_split_fixedField_of_normal` proves the same equivalence for any
normal subgroup. There are no signature changes to the requested theorem.
Existing admissions are unchanged.

The proof restricts the Frobenius residue congruence to the fixed field, descends
unramifiedness, and uses B1 to compare orders with the chosen Frobenius downstairs.
The kernel of restriction is the subgroup by Mathlib's finite Galois correspondence.

## Axiom audit

Checked at 2026-09-27 15:06 UTC with `lake env lean /tmp/chebotarev-h2-axioms.lean`
(exit 0). Each of the five new theorems depends exactly on
`[propext, Classical.choice, Quot.sound]`; none depends on `sorryAx`.

Reproduce with this Lean file:

```lean
import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.SubfieldSplitting

#print axioms GaloisRepresentation.Chebotarev.unram_intermediateField
#print axioms GaloisRepresentation.Chebotarev.isArithFrobAt_restrictNormal
#print axioms GaloisRepresentation.Chebotarev.restrictNormal_frob_eq_one_iff
#print axioms GaloisRepresentation.Chebotarev.frob_mem_iff_split_fixedField_of_normal
#print axioms GaloisRepresentation.Chebotarev.frob_mem_iff_split_fixedField
```

Both build commands passed on 2026-09-27; the full build completed all 9,533 jobs.
The public imports in `FLT.lean` are in `LC_ALL=C` order, and `git diff --check` passed.
No full `lake lint` was run, as directed by the brief.

```sh
LEAN_NUM_THREADS=4 lake build FLT.GaloisRepresentation.HardlyRamified.Chebotarev.SubfieldSplitting
LEAN_NUM_THREADS=4 lake build
```
