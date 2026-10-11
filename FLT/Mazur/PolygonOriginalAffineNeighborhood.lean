/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalAffineScalars
public import FLT.Mazur.PolygonOriginalAffineTransition
public import FLT.Mazur.SurjectiveIdealPowerQuotient

/-!
# Point neighborhoods recovered from the actual original stages

For any affine ideal containing the original parameter, its (m+1)-st
power neighborhood is already visible on the m-th original polygon stage.
In particular this applies to the ideal of any point of the closed fiber.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family exactVeroneseProj originalStageToCompatibleProj
  originalStageAffineTransition

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (U : (exactVeroneseProj K n h).affineOpens)

/-- The original image of an affine ideal on a finite polygon stage. -/
def originalStageAffineIdeal (m : ℕ) (J : Ideal Γ(exactVeroneseProj K n h, U)) :
    Ideal Γ((family K m n h).left, originalStageToCompatibleProj K n h m ⁻¹ᵁ U) :=
  J.map ((originalStageToCompatibleProj K n h m).app U).hom

/-- Original stage transitions preserve the image of the affine ideal exactly. -/
theorem originalStageAffineIdeal_transition {a b : ℕ} (f : a ⟶ b)
    (J : Ideal Γ(exactVeroneseProj K n h, U)) :
    (originalStageAffineIdeal K n h U b J).map (originalStageAffineTransition K n h f U) =
      originalStageAffineIdeal K n h U a J := by
  rw [originalStageAffineIdeal, originalStageAffineIdeal, Ideal.map_map]
  congr 1
  ext s
  exact originalStageAffineTransition_app K n h f U s

/-- An ideal containing the actual parameter contains the affine adic ideal. -/
theorem compatibleProjAdicIdeal_le_of_parameter_mem
    (J : Ideal Γ(exactVeroneseProj K n h, U))
    (hq : completeAffineScalars K n h U PowerSeries.X ∈ J) :
    (compatibleProjAdicIdeal K n h).ideal U ≤ J := by
  rw [compatibleProjAdicIdeal_affine]
  exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hq)

/-- The complete point neighborhood is the actual neighborhood on its original stage. -/
def originalStageNeighborhoodQuotient (m : ℕ)
    (J : Ideal Γ(exactVeroneseProj K n h, U))
    (hq : completeAffineScalars K n h U PowerSeries.X ∈ J) :
    (Γ(exactVeroneseProj K n h, U) ⧸ J ^ (m + 1)) ≃+*
      (Γ((family K m n h).left, originalStageToCompatibleProj K n h m ⁻¹ᵁ U) ⧸
        originalStageAffineIdeal K n h U m J ^ (m + 1)) :=
  SurjectiveIdealPowerQuotient.equivalence _ (originalStage_app_surjective K n h m U)
    J (m + 1) (by
      rw [originalStage_app_ker]
      exact pow_le_pow_left' (compatibleProjAdicIdeal_le_of_parameter_mem K n h U J hq) _)

/-- The neighborhood comparison is induced by the actual stage section map. -/
@[simp] theorem originalStageNeighborhoodQuotient_mk (m : ℕ)
    (J : Ideal Γ(exactVeroneseProj K n h, U))
    (hq : completeAffineScalars K n h U PowerSeries.X ∈ J)
    (s : Γ(exactVeroneseProj K n h, U)) :
    originalStageNeighborhoodQuotient K n h U m J hq (Ideal.Quotient.mk _ s) =
      Ideal.Quotient.mk _ ((originalStageToCompatibleProj K n h m).app U s) :=
  SurjectiveIdealPowerQuotient.equivalence_mk _ _ _ _ _ s

/-- All complete-base coefficients are retained in the point-neighborhood comparison. -/
theorem originalStageNeighborhoodQuotient_scalars (m : ℕ)
    (J : Ideal Γ(exactVeroneseProj K n h, U))
    (hq : completeAffineScalars K n h U PowerSeries.X ∈ J) (r : PowerSeries K) :
    originalStageNeighborhoodQuotient K n h U m J hq
      (Ideal.Quotient.mk _ (completeAffineScalars K n h U r)) =
        Ideal.Quotient.mk _ (originalStageAffineScalars K n h m U r) := by
  rw [originalStageNeighborhoodQuotient_mk, originalStage_app_scalars]

end FLT.Mazur.PolygonInfinitesimalStages
