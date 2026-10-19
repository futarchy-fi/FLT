/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationScalarLocalEquations
public import FLT.Mazur.EquivalenceRelationCompleteCharacterLifts
public import FLT.Mazur.InvariantScalarGoingDown

/-!
# Original complete geometry from minimal scalar branches

Source flatness transports complete generic-character geometry to every
prime below the original scalar center. The original frame size, all original
relation branches and all scalar-test nilpotents remain unchanged. Generic
completeness and flatness are independent inputs, not constructed here.
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

/-- Complete lifts on minimal scalar branches force containment at all local characters. -/
theorem complete_ideal_of_minimal_source_flat (hs : s.FiniteType)
    (hf : (invariantScalarCoordinates ρ s).Flat)
    (hc : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ minimalPrimes R → Q ≤ P →
      ∀ χ : invariantCoordinates ρ →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp s = algebraMap R _ →
        ∃ w : Γ(U.toScheme, ⊤) →+* AlgebraicClosure Q.asIdeal.ResidueField,
          (∀ t : invariantCoordinates ρ, w t.val = χ t) ∧
          Complete I o (sourceCharacterMap w ≫ U.ι))
    (Q : PrimeSpectrum R) (hQP : Q ≤ P)
    (χ : invariantCoordinates ρ →+* AlgebraicClosure Q.asIdeal.ResidueField)
    (hχ : χ.comp s = algebraMap R _) : J ≤ RingHom.ker χ := by
  apply invariant_ideal_le_character_of_minimal_source_flat ρ s P J hs hf _ Q hQP χ hχ
  intro Q hQ hQP χ hχ t ht
  obtain ⟨w, hw, hwc⟩ := hc Q hQ hQP χ hχ
  exact (hw t).symm.trans ((complete_character_iff_orbit_ideal e I o U hU w).mp hwc t ht)

/-- The same generic geometry controls all scalar tests supported below the original prime. -/
theorem scalarTestRelation_equalizes_of_minimal_source_flat [IsLocallyNoetherian A]
    (hs : s.FiniteType) (hf : (invariantScalarCoordinates ρ s).Flat)
    (hJ : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ minimalPrimes R → Q ≤ P →
      ∀ χ : invariantCoordinates ρ →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp s = algebraMap R _ → J ≤ RingHom.ker χ)
    {T : Scheme} (b : T ⟶ Spec (.of R)) (hb : ∀ x : T, (b x : PrimeSpectrum R).asIdeal ≤ P.asIdeal)
    (t : invariantCoordinates ρ) :
    (scalarTestRelationMap e I o U hU s b ≫ F).appTop t.val =
      (scalarTestRelationMap e I o U hU s b ≫ H).appTop t.val := by
  apply scalarTestRelation_equalizes_over_primes e I o U hU s hs
    {Q | Q.asIdeal ≤ P.asIdeal} _ b hb t
  exact invariant_ideal_le_character_of_minimal_source_flat ρ s P J hs hf hJ

/-- Minimal scalar branches suffice for exact equations on the full unreduced localization. -/
theorem scalarLocalRelation_equalizes_of_minimal_source_flat [IsLocallyNoetherian A]
    (hs : s.FiniteType) (hf : (invariantScalarCoordinates ρ s).Flat)
    (hJ : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ minimalPrimes R → Q ≤ P →
      ∀ χ : invariantCoordinates ρ →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp s = algebraMap R _ → J ≤ RingHom.ker χ) (t : invariantCoordinates ρ) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime P.asIdeal)))
    (scalarTestRelationMap e I o U hU s b ≫ F).appTop t.val =
      (scalarTestRelationMap e I o U hU s b ≫ H).appTop t.val := by
  apply scalarLocalRelation_equalizes e I o U hU s P hs _ t
  exact invariant_ideal_le_character_of_minimal_source_flat ρ s P J hs hf hJ

end FLT.Mazur.EquivalenceRelationNormalizedFrames
