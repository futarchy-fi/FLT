/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarGeometricOpenLift

/-!
# Sealed original scalar residue closures for geometric constructions

This is the canonical algebraic closure of the original residue field, with
its unchanged scalar action. Sealing the type and its instances prevents
expansion of invariant-sheaf equalizers during geometric elaboration.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
open SchemeFiniteGroupQuotient SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]

/-- The canonical geometric field of the unchanged original scalar prime. -/
def scalarResidueClosure (P : PrimeSpectrum R) : Type :=
  AlgebraicClosure P.asIdeal.ResidueField

instance scalarResidueClosureField (P : PrimeSpectrum R) : Field (scalarResidueClosure P) :=
  inferInstanceAs (Field (AlgebraicClosure P.asIdeal.ResidueField))

instance scalarResidueClosureAlgebra (P : PrimeSpectrum R) : Algebra R (scalarResidueClosure P) :=
  inferInstanceAs (Algebra R (AlgebraicClosure P.asIdeal.ResidueField))

instance scalarResidueClosureClosed (P : PrimeSpectrum R) : IsAlgClosed (scalarResidueClosure P) :=
  inferInstanceAs (IsAlgClosed (AlgebraicClosure P.asIdeal.ResidueField))

/-- The sealed field has precisely the original scalar center. -/
theorem scalarResidueClosure_center (P : PrimeSpectrum R) :
    PrimeSpectrum.comap (algebraMap R (scalarResidueClosure P)) ⊥ = P := by
  unfold scalarResidueClosure
  exact ScalarTestLocalization.algebraicClosure_residue_center P

variable {X : Scheme} [IsAffine X] [IsLocallyNoetherian X]
  (s : R →+* Γ(X, ⊤)) (P : PrimeSpectrum R) {Y : Scheme} (g : Y ⟶ X)
  [LocallyOfFinitePresentation g] [LocallyQuasiFinite g] [IsSeparated g] [QuasiCompact g]

/-- Sealing retains the constructed full-character lift in the finite target locus. -/
theorem exists_minimal_scalar_sealed_character (hs : s.FiniteType)
    (hi : Function.Injective s) (hP : P.asIdeal ∈ minimalPrimes R) :
    ∃ w : Γ(X, ⊤) →+* scalarResidueClosure P,
      w.comp s = algebraMap R (scalarResidueClosure P) ∧
      sourceCharacterMap w default ∈ finiteTargetOpen g := by
  exact exists_minimal_scalar_finite_character s P g hs hi hP

attribute [irreducible] scalarResidueClosure

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
