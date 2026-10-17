/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAffineCompletionLift
public import FLT.Mazur.AdicCompletionSeparatedExt
public import FLT.Mazur.PolygonCompleteIdentityActionLocalGluing

/-!
# The constructed completed action satisfies the original cubic equation

Each original finite action retains the cubic relation. Separatedness detects
that relation on the actual completion, including all nilpotent coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (U : (completeIdentityActionProduct K n h 0).affineOpens)
  (V : (exactVeroneseProj K n h).affineOpens)
  (hUV : completeIdentityFiniteInput K n h 0 0 ⁻¹ᵁ U.1 ≤
    completeIdentityFiniteScaling K n h 0 ⁻¹ᵁ V.1)
local notation "v" => completeIdentityAffineSourceMap K n h U
local notation "R" => completeIdentityAffineSourceRing K n h U
local notation "I" => completeIdentityAffineIdeal K n h (A := (R)) (v)
local notation "d" => Spec.map (CommRingCat.ofHom (algebraMap (R) (AdicCompletion (I) (R))))
local notation "c" => completePointToIntegralCubic K n h 0
local notation "a" => completeIdentityActionTarget K n h 0

/-- Completion evaluations keep the original affine source's quotient inclusions. -/
@[reassoc] theorem completeIdentityAffineCompletion_evaluation_input (m : ℕ) :
    Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ (I) (m + 1)).toRingHom) ≫ (d) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I) ^ (m + 1)))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1

/-- The constructed completed polygon map satisfies the unchanged original cubic equation. -/
@[reassoc] theorem completeIdentityAffineCompletionLift_cubic :
    completeIdentityAffineCompletionLift K n h U V hUV ≫ (c) = (d) ≫ (v) ≫ (a) := by
  let W := completePointWeierstrassCurve K n h 0
  let _ : IsSeparated (terminal.from (integralCurve W)) := by
    rw [← terminal.comp_from (integralCurveStructure W)]
    infer_instance
  apply AdicCompletionSeparatedExt.hom_ext (I) (terminal.from (integralCurve W))
    (terminal.hom_ext _ _)
  intro m
  rw [completeIdentityAffineCompletionLift_evaluation_assoc,
    Category.assoc, completeIdentityFiniteComparison_all,
    completeIdentityAffineQuotientToFinite_input_assoc,
    completeIdentityAffineCompletion_evaluation_input_assoc]
  simp only [completeIdentityAffineSourceMap, Category.assoc]

/-- The actual completed lift also preserves the original complete coefficient structure. -/
@[reassoc] theorem completeIdentityAffineCompletionLift_structure :
    completeIdentityAffineCompletionLift K n h U V hUV ≫ exactVeroneseProjToBase K n h =
      (d) ≫ (v) ≫ completeIdentityActionSecond K n h ≫ exactVeroneseProjToBase K n h := by
  exact completeIdentityActionLift_structure K n h ((d) ≫ (v)) _
    (by simpa only [Category.assoc] using completeIdentityAffineCompletionLift_cubic K n h U V hUV)

end FLT.Mazur.PolygonInfinitesimalStages
