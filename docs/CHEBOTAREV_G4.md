# G4: the chosen local Frobenius

Implementation: `FLT/GaloisRepresentation/HardlyRamified/Chebotarev/LocalFrobenius.lean`.

Checked at 2026-09-27 15:28 UTC: the module build, full `lake build`, axiom
audit, and expression check below all exited 0. The full build completed
9535 jobs. `git diff --check` passed, and the public imports in `FLT.lean`
were checked against bytewise (`LC_ALL=C`) ordering.

`hasFrob_restrict_QFrob` has the plan's signature, including unramifiedness.
`isConj_restrict_QFrob_frob` compares this restriction with `frob ℚ L vq`.
Both take a finite Galois intermediate field of `AlgebraicClosure ℚ`.
Existing admissions are unchanged; this proves G4, not Chebotarev density.

The congruence proof works over any number field. It uses
`localIntegersMap_equivariant` and the residue-field equivalence between a
global prime and its completion. Equating the two residue cardinalities
directly avoids separately computing each as `q` in the rational case.
`localInducedPrime_liesOver` supplies the prime contraction, so the proof
uses the same chosen closure embedding throughout. Conjugacy follows from
transitivity on primes, transport of Frobenius by conjugation, and trivial
inertia at an unramified prime.

The brief says `QFrob` already exists in `B5Inputs.lean`; it was absent in
this checkout. The new module defines `GaloisRepresentation.B5Inputs.QFrob`
as the plan's exact expression, with B5's completion-instance priorities.
The `HasFrob` predicate is also introduced here. The stronger auxiliary
`isArithFrobAt_restrict_QFrob` does not need unramifiedness.

Reproduce the builds:

```sh
LEAN_NUM_THREADS=4 lake build FLT.GaloisRepresentation.HardlyRamified.Chebotarev.LocalFrobenius
LEAN_NUM_THREADS=4 lake build
```

Reproduce the axiom audit and the check of B5's chosen expression:

```sh
cat > /tmp/chebotarev-g4-audit.lean <<'LEAN'
import FLT.GaloisRepresentation.HardlyRamified.B5Inputs
import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.LocalFrobenius
#print axioms GaloisRepresentation.Chebotarev.isArithFrobAt_localRestriction
#print axioms GaloisRepresentation.Chebotarev.qFrobPrime_under
#print axioms GaloisRepresentation.Chebotarev.isArithFrobAt_restrict_QFrob
#print axioms GaloisRepresentation.Chebotarev.hasFrob_restrict_QFrob
#print axioms GaloisRepresentation.Chebotarev.isConj_frob_of_hasFrob
#print axioms GaloisRepresentation.Chebotarev.isConj_restrict_QFrob_frob
open IsDedekindDomain
attribute [local instance 2000] HeightOneSpectrum.adicCompletion.instField
  HeightOneSpectrum.instAlgebraAdicCompletion
example (q : ℕ) (hq : q.Prime) :
    GaloisRepresentation.B5Inputs.QFrob q hq =
      Field.absoluteGaloisGroup.map
        (algebraMap ℚ (hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ))
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat) := rfl
LEAN
LEAN_NUM_THREADS=4 lake env lean /tmp/chebotarev-g4-audit.lean
```

Every theorem above reports exactly `[propext, Classical.choice, Quot.sound]`;
none depends on `sorryAx` or a new axiom. The expression comparison closes by
`rfl`, so it does not replace the chosen embedding.
