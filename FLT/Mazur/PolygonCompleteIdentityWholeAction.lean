/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityOriginalInputCover

/-!
# The action on the entire original complete input

The smooth-input open and the constructed affine neighborhoods of original
closed inputs form an actual cover. Their lifts glue, without any additional
existence or overlap hypotheses, to the entire original action product.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => completeIdentityActionProduct K n h 0
local notation "Z" => PolygonInfinitesimal.scalingParameterFamily
  (Ring K 0) (parameter K 0) n h
local notation "X" => exactVeroneseProj K n h
local notation "c" => completePointToIntegralCubic K n h 0
local notation "a" => completeIdentityActionTarget K n h 0

/-- Choose the already constructed original affine action neighborhood at a closed input. -/
def completeIdentityClosedActionAffine (z : Z) : (P).affineOpens :=
  (completeIdentityAffineOpenLift_exists K n h z).choose

/-- The chosen affine neighborhood carries an actual polygon-valued action. -/
def completeIdentityClosedActionLift (z : Z) :
    (completeIdentityClosedActionAffine K n h z).1.toScheme ⟶ (X) :=
  (completeIdentityAffineOpenLift_exists K n h z).choose_spec.choose

/-- The chosen neighborhood contains its original closed input. -/
theorem completeIdentityClosedActionAffine_mem (z : Z) :
    completeIdentityFiniteInput K n h 0 0 z ∈
      (completeIdentityClosedActionAffine K n h z).1 :=
  (completeIdentityAffineOpenLift_exists K n h z).choose_spec.choose_spec.1

/-- The chosen local action retains the prescribed original cubic map. -/
@[reassoc] theorem completeIdentityClosedActionLift_cubic (z : Z) :
    completeIdentityClosedActionLift K n h z ≫ (c) =
      (completeIdentityClosedActionAffine K n h z).1.ι ≫ (a) :=
  (completeIdentityAffineOpenLift_exists K n h z).choose_spec.choose_spec.2

/-- Explicit original domains: the smooth open and one constructed affine per closed input. -/
def completeIdentityWholeActionOpen : Option (Z) → (P).Opens
  | none => completeIdentityActionSmoothOpen K n h
  | some z => (completeIdentityClosedActionAffine K n h z).1

/-- These original domains cover every original input, including every singular input. -/
def completeIdentityWholeActionCover : (P).OpenCover where
  I₀ := Option (Z)
  «X» i := (completeIdentityWholeActionOpen K n h i).toScheme
  f i := (completeIdentityWholeActionOpen K n h i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun _ ↦ inferInstance⟩
    by_cases hx : x ∈ completeIdentityActionSmoothOpen K n h
    · exact ⟨none, ⟨x, hx⟩, rfl⟩
    · obtain ⟨z, rfl⟩ := completeIdentityOriginalClosedInput_of_not_smooth K n h x hx
      exact ⟨some z, ⟨_, completeIdentityClosedActionAffine_mem K n h z⟩, rfl⟩

/-- Each member of the actual full-input cover has its constructed action. -/
def completeIdentityWholeActionLocal :
    ∀ i, (completeIdentityWholeActionCover K n h).X i ⟶ (X)
  | none => completeIdentityActionSmoothLift K n h
  | some z => completeIdentityClosedActionLift K n h z

/-- Every local action has the identical prescribed cubic target. -/
@[reassoc] theorem completeIdentityWholeActionLocal_cubic
    (i : (completeIdentityWholeActionCover K n h).I₀) :
    completeIdentityWholeActionLocal K n h i ≫ (c) =
      (completeIdentityWholeActionCover K n h).f i ≫ (a) := by
  cases i with
  | none => exact completeIdentityActionSmoothLift_contraction K n h
  | some z => exact completeIdentityClosedActionLift_cubic K n h z

/-- The constructed polygon-valued action on the entire original complete input product. -/
def completeIdentityWholeAction : (P) ⟶ (X) :=
  completeIdentityActionGlue K n h (completeIdentityWholeActionCover K n h)
    (completeIdentityWholeActionLocal K n h) (completeIdentityWholeActionLocal_cubic K n h)

/-- The global action retains each of the constructed original local lifts. -/
@[reassoc] theorem completeIdentityWholeAction_chart
    (i : (completeIdentityWholeActionCover K n h).I₀) :
    (completeIdentityWholeActionCover K n h).f i ≫ completeIdentityWholeAction K n h =
      completeIdentityWholeActionLocal K n h i :=
  completeIdentityActionGlue_chart K n h _ _ _ i

/-- The entire original action contracts to the unchanged cubic action. -/
@[reassoc] theorem completeIdentityWholeAction_cubic :
    completeIdentityWholeAction K n h ≫ (c) = (a) :=
  completeIdentityActionGlue_contraction K n h _ _ _

/-- The entire original action preserves its original power-series base. -/
@[reassoc] theorem completeIdentityWholeAction_structure :
    completeIdentityWholeAction K n h ≫ exactVeroneseProjToBase K n h =
      completeIdentityActionSecond K n h ≫ exactVeroneseProjToBase K n h := by
  simpa only [Category.id_comp] using completeIdentityActionLift_structure K n h (𝟙 (P))
    (completeIdentityWholeAction K n h)
    (by simpa only [Category.id_comp] using completeIdentityWholeAction_cubic K n h)

end FLT.Mazur.PolygonInfinitesimalStages
