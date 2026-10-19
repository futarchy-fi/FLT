/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationWholeScalarStrata
public import FLT.Mazur.EquivalenceRelationCompleteScalarStrata

/-!
# Actual residue-character witnesses for excluded scalar primes

A scalar prime in the actual image but outside the whole-complete locus has an
incomplete source character over its own residue closure. A specific complete
orbit equation fails there, so this detects missing coverage by actual geometry.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarPrincipalNeighborhood
open ScalarClosedImageCoverage
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (B : (source p q I o).Opens)
  (hB : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme]
local notation "ρ" => restrictedAction (action e I o) B hB
local notation "C" => invariantCoordinates ρ
local notation "i" => invariantScalarCoordinates ρ (RingHom.id C)
local notation "J" => completeAffineOrbitIdeal e I o B hB
local notation "u" w => sourceCharacterMap (X := B.toScheme) w ≫ B.ι
attribute [local irreducible] source action restrictedAction Complete
attribute [local semireducible] scalarResidueClosure

variable {R : Type} [CommRing R]
  (σ : R →+* invariantCoordinates (restrictedAction (action e I o) B hB))
local notation "s" => invariantScalarCoordinates ρ σ
local notation "K" P => scalarResidueClosure P

/-- An excluded prime in the actual scalar image has an exact incomplete residue character. -/
theorem exists_incomplete_scalar_defect_character (hs : σ.FiniteType) (P : PrimeSpectrum R)
    (hr : P ∈ Set.range (PrimeSpectrum.comap σ))
    (hP : P ∉ wholeCompleteScalarLocus e I o B hB σ) :
    ∃ w : Γ(B.toScheme, ⊤) →+* K P,
      w.comp s = algebraMap R (K P) ∧ ¬ Complete I o (u w) ∧
        ∃ t ∈ J, w t.val ≠ 0 := by
  have hb : P ∈ PrimeSpectrum.comap σ ''
      (completeAffineOrbitImage e I o B hB : Set (quotient ρ))ᶜ := by
    by_contra hn
    apply hP
    rw [wholeCompleteScalarLocus]
    exact ⟨hr, hn⟩
  obtain ⟨Q, hQ, hQP⟩ := hb
  have hn : ¬ (J : Set C) ⊆ Q.asIdeal := by
    intro hj
    apply hQ
    change Q ∈ (completeAffineOrbitImage e I o B hB : Set (quotient ρ))
    rw [← completeAffineOrbitIdeal_zeroLocus]
    exact hj
  obtain ⟨t, ht, htQ⟩ := Set.not_subset.mp hn
  obtain ⟨χ, hχ, hχt⟩ := ScalarTestLocalization.exists_residue_geometric_failure
    σ P hs t Q hQP htQ
  obtain ⟨w, hw⟩ := exists_sourceCharacter_lift ρ χ
  have hwt : w t.val ≠ 0 := by rwa [hw]
  refine ⟨w, ?_, ?_, t, ht, hwt⟩
  · ext r
    change w (σ r).val = _
    rw [hw]
    exact DFunLike.congr_fun hχ r
  · intro hc
    have hz := (complete_character_iff_closed_equations e I o B hB w).mp hc
      (i t) (Ideal.mem_map_of_mem i ht)
    exact hwt hz

end FLT.Mazur.EquivalenceRelationNormalizedFrames
