/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationInvariantCharacterFibers

/-!
# Construct complete frames over the closed invariant quotient

The actual complete-orbit ideal detects completeness of every field-valued
lift. Characters of its quotient have constructed complete representatives
and unique original arrows to every other lift, with the original labels.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] {K : Type} [Field K]
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "J" => completeAffineOrbitIdeal e I o U hU
local notation "u" w => sourceCharacterMap (X := U.toScheme) w ≫ U.ι

/-- Completeness of an actual lift is exactly vanishing of the original orbit ideal. -/
theorem complete_character_iff_orbit_ideal (w : Γ(U.toScheme, ⊤) →+* K) :
    Complete I o (u w) ↔ ∀ t ∈ J, w t.val = 0 := by
  rw [complete_iff_mem_completePointLocus]
  change sourceCharacterMap w default ∈
    U.ι ⁻¹' completePointLocus (p := p) (q := q) I o ↔ _
  rw [← completeAffineOrbitImage_preimage e I o U hU]
  change quotientMap ρ (sourceCharacterMap w default) ∈
    (completeAffineOrbitImage e I o U hU : Set _) ↔ _
  rw [← completeAffineOrbitIdeal_zeroLocus]
  change (∀ t ∈ J, t ∈ (quotientMap ρ (sourceCharacterMap w default)).asIdeal) ↔ _
  rw [← Scheme.Hom.comp_apply, sourceCharacterMap_quotient]
  rfl

variable [IsAlgClosed K]

/-- Vanishing of the orbit ideal constructs a complete original representative. -/
theorem exists_complete_character_lift
    (χ : invariantCoordinates (restrictedAction (action e I o) U hU) →+* K)
    (hχ : J ≤ RingHom.ker χ) :
    ∃ w : Γ(U.toScheme, ⊤) →+* K,
      (∀ t : invariantCoordinates ρ, w t.val = χ t) ∧ Complete I o (u w) := by
  obtain ⟨w, hw⟩ := exists_sourceCharacter_lift ρ χ
  refine ⟨w, hw, (complete_character_iff_orbit_ideal e I o U hU w).mpr ?_⟩
  intro t ht
  exact (hw t).trans (hχ ht)

/-- Every character of the actual closed quotient has a complete original orbit. -/
theorem exists_complete_quotient_character_orbit
    (χ : (invariantCoordinates ρ ⧸ J) →+* K) :
    ∃ w : Γ(U.toScheme, ⊤) →+* K,
      (∀ t : invariantCoordinates ρ, w t.val = χ (Ideal.Quotient.mk J t)) ∧
      Complete I o (u w) ∧
      ∀ v : Γ(U.toScheme, ⊤) →+* K,
        (∀ t : invariantCoordinates ρ, v t.val = χ (Ideal.Quotient.mk J t)) →
        Complete I o (u v) ∧
          ∃! a : Spec (.of K) ⟶ D,
            a ≫ p = (u w) ≫ first p q I o ∧
            a ≫ q = (u v) ≫ first p q I o := by
  have hχ : J ≤ RingHom.ker (χ.comp (Ideal.Quotient.mk J)) := by
    intro t ht
    change χ (Ideal.Quotient.mk J t) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ht, map_zero]
  obtain ⟨w, hw, hc⟩ := exists_complete_character_lift e I o U hU
    (χ.comp (Ideal.Quotient.mk J)) hχ
  refine ⟨w, hw, hc, fun v hv ↦ ?_⟩
  have he : ∀ t : invariantCoordinates ρ, w t.val = v t.val :=
    fun t ↦ (hw t).trans (hv t).symm
  exact ⟨complete_of_invariant_character e I o U hU w v he hc,
    invariant_character_original_arrow e I o U hU w v he⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
