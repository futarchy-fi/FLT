/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAffineCompletionCubic
public import FLT.Mazur.PolygonCompleteIdentityGenericAffineLift
public import FLT.Mazur.PolygonCompleteIdentityCompletionDescent

/-!
# Original open actions from completed and generic lifts

The constructed completed and generic maps make the entire original graph
invertible over each selected affine input. Its inverse gives an actual
polygon-valued action on an original open neighborhood of every closed input.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
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
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "c" => completePointToIntegralCubic K n h 0
local notation "a" => completeIdentityActionTarget K n h 0

include V hUV in
/-- Completed and generic constructions invert the full original graph over the selected input. -/
theorem completeIdentityAffineGraph_isIso : IsIso (pullback.snd (p) (v)) := by
  let _ : IsNoetherianRing (R) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩
  let _ : Flat (v) := by
    dsimp only [completeIdentityAffineSourceMap]
    infer_instance
  let P (J : Ideal (R)) : Prop := ∃ F :
      Spec (.of (AdicCompletion J (R))) ⟶ exactVeroneseProj K n h,
    F ≫ (c) = Spec.map (CommRingCat.ofHom (algebraMap (R) (AdicCompletion J (R)))) ≫
      (v) ≫ (a)
  have hP : P (completeIdentityAffineIdeal K n h (A := (R)) (v)) :=
    ⟨completeIdentityAffineCompletionLift K n h U V hUV,
      completeIdentityAffineCompletionLift_cubic K n h U V hUV⟩
  have hP' := (congrArg P (completeIdentityAffineIdeal_eq K n h (A := (R)) (v))).mp hP
  obtain ⟨F, hF⟩ := hP'
  exact completeIdentityActionCompletion_graph_isIso K n h («R» := (R)) (v)
    (completeIdentityAffineScalars K n h (A := (R)) (v) PowerSeries.X) F hF
    (completeIdentityGenericAffineLift K n h (A := (R)) (v))
    (completeIdentityGenericAffineLift_cubic K n h (A := (R)) (v))

/-- The graph inverse constructs the actual action on the original affine open. -/
def completeIdentityAffineOpenLift : U.1.toScheme ⟶ exactVeroneseProj K n h :=
  let _ := completeIdentityAffineGraph_isIso K n h U V hUV
  U.1.toScheme.isoSpec.hom ≫ inv (pullback.snd (p) (v)) ≫ pullback.fst (p) (v) ≫ (l)

/-- This is a lift of the unchanged cubic action on the entire original affine open. -/
@[reassoc] theorem completeIdentityAffineOpenLift_cubic :
    completeIdentityAffineOpenLift K n h U V hUV ≫ (c) = U.1.ι ≫ (a) := by
  let _ := completeIdentityAffineGraph_isIso K n h U V hUV
  rw [completeIdentityAffineOpenLift, Category.assoc, Category.assoc, Category.assoc,
    completeIdentityActionGraphLift_contraction, pullback.condition_assoc,
    IsIso.inv_hom_id_assoc]
  simp only [completeIdentityAffineSourceMap, Category.assoc, Iso.hom_inv_id_assoc]

/-- Every original closed input has a genuine action on an original affine neighborhood. -/
theorem completeIdentityAffineOpenLift_exists
    (z : PolygonInfinitesimal.scalingParameterFamily
      (Ring K 0) (parameter K 0) n h) :
    ∃ (W : (completeIdentityActionProduct K n h 0).affineOpens)
      (F : W.1.toScheme ⟶ exactVeroneseProj K n h),
      completeIdentityFiniteInput K n h 0 0 z ∈ W.1 ∧ F ≫ (c) = W.1.ι ≫ (a) := by
  obtain ⟨W, T, hzW, _, hWT⟩ := completeIdentityFiniteAffine_exists K n h z
  exact ⟨W, completeIdentityAffineOpenLift K n h W T (hWT 0), hzW,
    completeIdentityAffineOpenLift_cubic K n h W T (hWT 0)⟩

end FLT.Mazur.PolygonInfinitesimalStages
