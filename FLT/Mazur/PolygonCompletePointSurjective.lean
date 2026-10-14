/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointGlobalFunctions
public import FLT.Mazur.ProperFunctionSheafSurjective

/-!
# Surjectivity of the original complete-base cubic contraction

The original proper morphism preserves all functions, so its image is the
entire original integral cubic, over the full complete base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "g" => completePointToIntegralCubic K n h i

/-- The unchanged complete-base contraction is surjective on the whole cubic. -/
theorem completePointToIntegralCubic_surjective : Surjective (g) := by
  let _ := completePointToIntegralCubic_proper K n h i
  apply ProperFunctionSheafSurjective.surjective (g)
  intro U
  let _ := completePointToIntegralCubic_app_isIso K n h i U
  exact (ConcreteCategory.bijective_of_isIso ((g).app U)).injective

/-- The original contraction reflects equality of target opens. -/
theorem completePointToIntegralCubic_preimage_injective :
    Function.Injective (fun U : (integralCurve (completePointWeierstrassCurve K n h i)).Opens ↦
      (g) ⁻¹ᵁ U) := by
  let _ := completePointToIntegralCubic_surjective K n h i
  intro U V hUV
  ext y
  obtain ⟨x, rfl⟩ := (inferInstance : Surjective (g)).1 y
  exact SetLike.ext_iff.mp hUV x

end FLT.Mazur.PolygonInfinitesimalStages
