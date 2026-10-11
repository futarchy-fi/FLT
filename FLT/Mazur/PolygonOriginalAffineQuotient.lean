/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalAdicRealization

/-!
# Affine quotients of the actual complete polygon

On every affine open of the complete candidate, restriction to an original
stage is the quotient by the corresponding power of the original parameter
ideal. The comparison uses the actual stage immersion and its section map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family exactVeroneseProj originalStageToCompatibleProj
  originalStageAdicIso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original stage immersion has exactly the original parameter-power ideal. -/
theorem originalStageToCompatibleProj_ker (m : ℕ) :
    (originalStageToCompatibleProj K n h m).ker =
      compatibleProjAdicIdeal K n h ^ (m + 1) := by
  rw [← originalStageAdicIso_hom_ι, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_subschemeι]

/-- On an affine open, the kernel is the corresponding power of its parameter ideal. -/
theorem originalStage_app_ker (m : ℕ) (U : (exactVeroneseProj K n h).affineOpens) :
    RingHom.ker ((originalStageToCompatibleProj K n h m).app U).hom =
      (compatibleProjAdicIdeal K n h).ideal U ^ (m + 1) := by
  let _ := originalStageToCompatibleProj_isClosedImmersion K n h m
  rw [← Scheme.Hom.ker_apply, originalStageToCompatibleProj_ker]
  rfl

/-- Every section on the original affine stage lifts to the complete affine open. -/
theorem originalStage_app_surjective (m : ℕ)
    (U : (exactVeroneseProj K n h).affineOpens) :
    Function.Surjective ((originalStageToCompatibleProj K n h m).app U) := by
  let _ := originalStageToCompatibleProj_isClosedImmersion K n h m
  exact Scheme.Hom.app_surjective (originalStageToCompatibleProj K n h m) U.1 U.2

/-- The actual affine quotient comparison, with the original restriction map. -/
def originalStageAffineQuotient (m : ℕ) (U : (exactVeroneseProj K n h).affineOpens) :
    (Γ(exactVeroneseProj K n h, U) ⧸
      (compatibleProjAdicIdeal K n h).ideal U ^ (m + 1)) ≃+*
        Γ((family K m n h).left, originalStageToCompatibleProj K n h m ⁻¹ᵁ U) :=
  (Ideal.quotEquivOfEq (originalStage_app_ker K n h m U).symm).trans
    (RingHom.quotientKerEquivOfSurjective (originalStage_app_surjective K n h m U))

/-- The comparison sends a quotient class to its actual original-stage restriction. -/
@[simp] theorem originalStageAffineQuotient_mk (m : ℕ)
    (U : (exactVeroneseProj K n h).affineOpens) (s : Γ(exactVeroneseProj K n h, U)) :
    originalStageAffineQuotient K n h m U (Ideal.Quotient.mk _ s) =
      (originalStageToCompatibleProj K n h m).app U s := by
  simp [originalStageAffineQuotient]

end FLT.Mazur.PolygonInfinitesimalStages
