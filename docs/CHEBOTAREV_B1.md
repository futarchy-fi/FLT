# B1: Frobenius order equals residue degree

Implementation: `FLT/GaloisRepresentation/HardlyRamified/Chebotarev/FrobeniusOrder.lean`.
The public namespace is `GaloisRepresentation.Chebotarev`.

`orderOf_frob_eq_inertiaDeg` has the signature proposed in
`CHEBOTAREV_PLAN.md`, with no extra arithmetic hypotheses. `Prime`, `Unram`,
`primeAbove`, and `frob` supply the proposed definitions. `frob_eq_one_iff`
proves the stated consequence for every prime above an unramified prime.
Existing admissions are unchanged.

The proof uses Mathlib's formula for the cardinality of inertia to show that
inertia is trivial at an unramified prime. The residue action is then injective
and preserves element orders. Mathlib's order formula for finite-field
Frobenius gives the residue degree. Constancy of residue degrees in a Galois
extension gives the formula for any prime above the base prime.

## Reproduce the checks

```sh
LEAN_NUM_THREADS=4 lake build FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FrobeniusOrder
LEAN_NUM_THREADS=4 lake build
```

To repeat the axiom audit, put the following in a temporary Lean file and run
`LEAN_NUM_THREADS=4 lake env lean /tmp/b1-axioms.lean`:

```lean
import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FrobeniusOrder
#print axioms GaloisRepresentation.Chebotarev.exists_primeAbove
#print axioms GaloisRepresentation.Chebotarev.primeAbove_under
#print axioms GaloisRepresentation.Chebotarev.isArithFrobAt_frob
#print axioms GaloisRepresentation.Chebotarev.inertia_eq_bot_of_isUnramifiedAt
#print axioms GaloisRepresentation.Chebotarev.orderOf_eq_inertiaDeg_of_isArithFrobAt
#print axioms GaloisRepresentation.Chebotarev.orderOf_frob_eq_inertiaDeg
#print axioms GaloisRepresentation.Chebotarev.frob_eq_one_iff
```

Checked at 2026-09-27 14:42 UTC: the module build and axiom audit both exited 0.
Each of the seven theorems printed exactly
`[propext, Classical.choice, Quot.sound]`; none depends on `sorryAx`.

Checked at 2026-09-27 14:46 UTC: the full `LEAN_NUM_THREADS=4 lake build`
exited 0 (`Build completed successfully (9529 jobs).`). `git diff --check`
passed, and the public imports in `FLT.lean` are sorted in `LC_ALL=C` order.
