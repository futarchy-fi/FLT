/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartAmbientTarget

/-!
# The unchanged target smoothing equation on the original full chart

Target functions have the same literal truncated-base parameter as the
source. Their product vanishes in the full closed fiber, before reduction
by any residual node ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "A" => Ring K 1
local notation "t" => parameter K 1
local notation "B" => ChartRing (t)
local notation "H" => completeIdentityActionGraphAdicChart K n h 1 0 0
local notation "s" => completeIdentityActionGraphAdicChartTarget K n h 1 0 0
local notation "p" => completeIdentityFirstChartTargetFunctions K n h
local notation "a" => completeIdentityActionGraphAdicChartScalars K n h 1 0 0
local notation "q" => completeIdentityFirstChartClosedQuotient K n h

/-- The target coefficient map is the original flat structure map of the full chart. -/
theorem completeIdentityFirstChartTargetFunctions_scalar (z : A) :
    (p) (algebraMap (A) (B) z) = (a) z := by
  have he := congrArg Scheme.Hom.appTop
    (completeIdentityActionGraphAdicChartTarget_structure K n h 1 0 0)
  have hh := congrArg (fun f : Γ(Spec (.of (A)), ⊤) ⟶ Γ((H), ⊤) ↦
    ((Scheme.ΓSpecIso (.of (A))).inv ≫ f) z) he
  rw [Scheme.Hom.comp_appTop] at hh
  change ((Scheme.ΓSpecIso (.of (A))).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap (A) (B)))).appTop ≫ (s).appTop) z = _ at hh
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality] at hh
  exact hh

/-- The original target coordinates have the same original smoothing parameter as the source. -/
theorem completeIdentityFirstChartTargetFunctions_xy :
    (p) (leftCoordinate (t)) * (p) (rightCoordinate (t)) =
      completeIdentityFirstChartParameter K n h := by
  rw [← map_mul, coordinate_relation, completeIdentityFirstChartTargetFunctions_scalar]
  rfl

/-- The target node equation holds in the full closed fiber, retaining its residual ideal. -/
theorem completeIdentityFirstChartClosedTarget_xy :
    (q) ((p) (leftCoordinate (t))) * (q) ((p) (rightCoordinate (t))) = 0 := by
  rw [← map_mul, completeIdentityFirstChartTargetFunctions_xy,
    completeIdentityFirstChartClosedQuotient_parameter]

end FLT.Mazur.PolygonInfinitesimalStages
