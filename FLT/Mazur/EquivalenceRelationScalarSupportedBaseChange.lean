/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationOriginalScalarFiber

/-!
# Full relation equations on infinitesimal original scalar tests

An arbitrary scalar scheme supported at the original prime retains all its
nilpotents. Full character containment puts its entire pulled relation in the
ambient zero-germ open, so equations hold before reducing the scalar test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient ScalarTestLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
local notation "k" => U.ι ≫ first p q I o
local notation "F" => SchemeRelationRestriction.fst p q k
local notation "H" => SchemeRelationRestriction.snd p q k
local notation "Rel" => SchemeRelationRestriction.doubleDomain p q k
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "J" => completeAffineOrbitIdeal e I o U hU
variable {R : Type} [CommRing R]
  (s : R →+* invariantCoordinates (restrictedAction (action e I o) U hU))
  (P : PrimeSpectrum R)
local notation "K" => AlgebraicClosure P.asIdeal.ResidueField
local notation "φ" => F ≫ quotientMap ρ ≫ Spec.map (CommRingCat.ofHom s)

/-- The whole original relation over an arbitrary scalar scheme, with both endpoints retained. -/
abbrev scalarTestRelation {T : Scheme} (b : T ⟶ Spec (.of R)) : Scheme := pullback φ b

/-- Forget only the scalar test coordinate, retaining the complete original relation arrow. -/
abbrev scalarTestRelationMap {T : Scheme} (b : T ⟶ Spec (.of R)) :
    scalarTestRelation e I o U hU s b ⟶ Rel := pullback.fst φ b

/-- Scalar support at the original prime controls all points of the unchanged relation. -/
theorem scalarTestRelation_complete (hs : s.FiniteType)
    (hJ : ∀ χ : invariantCoordinates ρ →+* K, χ.comp s = algebraMap R K →
      J ≤ RingHom.ker χ)
    {T : Scheme} (b : T ⟶ Spec (.of R)) (hb : ∀ x : T, b x = P) :
    Set.range (scalarTestRelationMap e I o U hU s b ≫ F ≫ quotientMap ρ) ⊆
      (completeAffineOrbitImage e I o U hU : Set (quotient ρ)) := by
  rw [← completeAffineOrbitIdeal_zeroLocus]
  rintro _ ⟨x, rfl⟩ t ht
  have hc := congrArg (fun a ↦ a x) (pullback.condition (f := φ) (g := b))
  change PrimeSpectrum.comap s
    ((scalarTestRelationMap e I o U hU s b ≫ F ≫ quotientMap ρ) x) =
      b (pullback.snd φ b x) at hc
  rw [hb] at hc
  apply (residueGeometricTest_iff_original_fiber s P hs t).mp _ _ hc
  exact (residueGeometricTest_iff s P t).mpr (fun χ hχ ↦ hJ χ hχ ht)

/-- Every infinitesimal scalar test over this prime satisfies the exact original equations. -/
theorem scalarTestRelation_equalizes [IsLocallyNoetherian A] (hs : s.FiniteType)
    (hJ : ∀ χ : invariantCoordinates ρ →+* K, χ.comp s = algebraMap R K →
      J ≤ RingHom.ker χ)
    {T : Scheme} (b : T ⟶ Spec (.of R)) (hb : ∀ x : T, b x = P)
    (t : invariantCoordinates ρ) :
    (scalarTestRelationMap e I o U hU s b ≫ F).appTop t.val =
      (scalarTestRelationMap e I o U hU s b ≫ H).appTop t.val :=
  completeOrbitSupportedTest_equalizes e I o U hU _
    (scalarTestRelation_complete e I o U hU s P hs hJ b hb) t

/-- The original residue field is enough for the equations; closure is only used for detection. -/
theorem residueScalarTestRelation_equalizes [IsLocallyNoetherian A] (hs : s.FiniteType)
    (hJ : ∀ χ : invariantCoordinates ρ →+* K, χ.comp s = algebraMap R K →
      J ≤ RingHom.ker χ) (t : invariantCoordinates ρ) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap R P.asIdeal.ResidueField))
    (scalarTestRelationMap e I o U hU s b ≫ F).appTop t.val =
      (scalarTestRelationMap e I o U hU s b ≫ H).appTop t.val := by
  apply scalarTestRelation_equalizes e I o U hU s P hs hJ _ _ t
  intro x
  apply PrimeSpectrum.ext
  ext r
  change algebraMap R P.asIdeal.ResidueField r ∈ x.asIdeal ↔ r ∈ P.asIdeal
  rw [Subsingleton.elim x (⊥ : PrimeSpectrum P.asIdeal.ResidueField)]
  exact Ideal.algebraMap_residueField_eq_zero

end FLT.Mazur.EquivalenceRelationNormalizedFrames
