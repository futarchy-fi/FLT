/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalAffineNeighborhood

/-!
# Compatible point-neighborhood quotients of the original polygon stages

The original polygon maps induce the transitions between all ideal-power
neighborhoods. The complete-family comparisons commute with these actual
transitions and preserve all original power-series coefficients.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family exactVeroneseProj originalStageToCompatibleProj
  originalStageAffineTransition originalStageNeighborhoodQuotient

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (U : (exactVeroneseProj K n h).affineOpens)
  (J : Ideal Γ(exactVeroneseProj K n h, U))

/-- Original transitions descend to the specified ideal-power neighborhoods. -/
def originalStageNeighborhoodTransition {a b : ℕ} (f : a ⟶ b) :
    (Γ((family K b n h).left, originalStageToCompatibleProj K n h b ⁻¹ᵁ U) ⧸
      originalStageAffineIdeal K n h U b J ^ (b + 1)) →+*
        (Γ((family K a n h).left, originalStageToCompatibleProj K n h a ⁻¹ᵁ U) ⧸
          originalStageAffineIdeal K n h U a J ^ (a + 1)) :=
  Ideal.quotientMap _ (originalStageAffineTransition K n h f U) (by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow, originalStageAffineIdeal_transition]
    exact Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f) 1))

/-- Neighborhood transitions keep the original stage restriction on representatives. -/
@[simp] theorem originalStageNeighborhoodTransition_mk {a b : ℕ} (f : a ⟶ b)
    (s : Γ((family K b n h).left, originalStageToCompatibleProj K n h b ⁻¹ᵁ U)) :
    originalStageNeighborhoodTransition K n h U J f (Ideal.Quotient.mk _ s) =
      Ideal.Quotient.mk _ (originalStageAffineTransition K n h f U s) := rfl

/-- Complete point neighborhoods are compatible with the actual original stage transitions. -/
theorem originalStageNeighborhoodQuotient_transition
    (hq : completeAffineScalars K n h U PowerSeries.X ∈ J)
    {a b : ℕ} (f : a ⟶ b) (s : Γ(exactVeroneseProj K n h, U) ⧸ J ^ (b + 1)) :
    originalStageNeighborhoodTransition K n h U J f
      (originalStageNeighborhoodQuotient K n h U b J hq s) =
        originalStageNeighborhoodQuotient K n h U a J hq
          (Ideal.Quotient.factor
            (Ideal.pow_le_pow_right (Nat.add_le_add_right (leOfHom f) 1)) s) := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [originalStageNeighborhoodQuotient_mk, originalStageNeighborhoodTransition_mk,
    originalStageAffineTransition_app, Ideal.Quotient.factor_mk,
    originalStageNeighborhoodQuotient_mk]

/-- Every section of a shallower neighborhood lifts to each deeper original neighborhood. -/
theorem originalStageNeighborhoodTransition_surjective
    (hq : completeAffineScalars K n h U PowerSeries.X ∈ J) {a b : ℕ} (f : a ⟶ b) :
    Function.Surjective (originalStageNeighborhoodTransition K n h U J f) := by
  intro s
  obtain ⟨r, rfl⟩ := (originalStageNeighborhoodQuotient K n h U a J hq).surjective s
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨originalStageNeighborhoodQuotient K n h U b J hq (Ideal.Quotient.mk _ r), ?_⟩
  rw [originalStageNeighborhoodQuotient_transition, Ideal.Quotient.factor_mk]

end FLT.Mazur.PolygonInfinitesimalStages
