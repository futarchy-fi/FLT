# Chebotarev B3 verification

The implementation is
`FLT/GaloisRepresentation/HardlyRamified/Chebotarev/NonsplitBound.lean`.
It proves `GaloisRepresentation.Chebotarev.primeSum_sub_splitPrimeSum_bounded`
with the B3 statement in `CHEBOTAREV_PLAN.md`, without added assumptions.

The proof reindexes the primes above `Split K L` using B2. The complement is
contained in the union of the ramified fibers and `HigherDegree K L`.
The former is finite by Mathlib's relative different-ideal criterion and
finite contraction fibers; D1 bounds the latter. D2 supplies the finite-set
bound. The finite-ramification helpers also apply to non-Galois extensions.

`FrobeniusOrder.lean` now imports D2's `NegligibleSets.lean` and reuses its
`Prime` abbreviation. Previously both files declared the same fully qualified
name, preventing B1/B2 and D1/D2 from being imported together. No admission or
existing theorem statement was changed. The public import in `FLT.lean` is in
C-locale order.

## Reproduce the checks

```sh
LEAN_NUM_THREADS=4 lake build FLT.GaloisRepresentation.HardlyRamified.Chebotarev.NonsplitBound
LEAN_NUM_THREADS=4 lake build
```

Run the following with `LEAN_NUM_THREADS=4 lake env lean FILE.lean`:

```lean
import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.NonsplitBound
#print axioms GaloisRepresentation.Chebotarev.primeBelow
#print axioms GaloisRepresentation.Chebotarev.primeBelowFiberEquiv
#print axioms GaloisRepresentation.Chebotarev.finite_primeBelow_fiber
#print axioms GaloisRepresentation.Chebotarev.finite_ramified_top
#print axioms GaloisRepresentation.Chebotarev.finite_ramified
#print axioms GaloisRepresentation.Chebotarev.finite_ramified_fibers
#print axioms GaloisRepresentation.Chebotarev.Split
#print axioms GaloisRepresentation.Chebotarev.splitPrimeEquiv
#print axioms GaloisRepresentation.Chebotarev.primeSum_split_fibers
#print axioms GaloisRepresentation.Chebotarev.nonsplit_subset_ramified_union_higherDegree
#print axioms GaloisRepresentation.Chebotarev.primeSum_sub_splitPrimeSum_bounded
```

Checked at 2026-09-27 15:11 UTC: the module build (3651 jobs), full build
(9538 jobs), and axiom audit all exited 0.
Every declaration above depends only on `[propext, Classical.choice, Quot.sound]`.
There is no `sorryAx` or new axiom. `git diff --check` and the public-import
ordering check also passed.

Axiom-audit output:

```text
'GaloisRepresentation.Chebotarev.primeBelow' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisRepresentation.Chebotarev.primeBelowFiberEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisRepresentation.Chebotarev.finite_primeBelow_fiber' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisRepresentation.Chebotarev.finite_ramified_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisRepresentation.Chebotarev.finite_ramified' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisRepresentation.Chebotarev.finite_ramified_fibers' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisRepresentation.Chebotarev.Split' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisRepresentation.Chebotarev.splitPrimeEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisRepresentation.Chebotarev.primeSum_split_fibers' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisRepresentation.Chebotarev.nonsplit_subset_ramified_union_higherDegree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GaloisRepresentation.Chebotarev.primeSum_sub_splitPrimeSum_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
