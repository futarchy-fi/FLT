/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointGlobalFunctions
public import FLT.Mazur.PolygonCompletePointOriginPositiveLine
public import FLT.Mazur.PointedStructureModuleComparison
public import FLT.Mazur.LinePullbackAdjunction

/-!
# Direct images of the original positive marking powers

The proved structure-sheaf comparison and projection formula recover each
original cubic-origin line from the original polygon marking power.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve WeierstrassIntegralChart ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "L" => completePointLine K n h i

/-- The original structure-module adjunction map is invertible on the full cubic. -/
theorem completePointToIntegralCubic_unitMap_isIso :
    IsIso (StructureDirectImage.unitMap (g)) := by
  apply PointedStructureModuleComparison.unitMap_isIso_of_app (g)
  intro V
  let _ := completePointToIntegralCubic_app_isIso K n h i V
  exact ConcreteCategory.bijective_of_isIso ((g).app V)

/-- Every original positive origin power is a line on the full cubic. -/
theorem completePointOriginLine_rankOne (m : ℕ) :
    LocallyFreeRankOne (originDivisorLine (W) m) :=
  (originIdealSheaf_power_effectiveCartier (W) m).divisorLineBundle_locallyFreeRankOne

/-- The actual unit for each original positive origin line is invertible. -/
theorem completePointOriginLine_unit_isIso (m : ℕ) :
    IsIso ((pullbackPushforwardAdjunction (g)).unit.app (originDivisorLine (W) m)) := by
  let _ := completePointToIntegralCubic_unitMap_isIso K n h i
  exact LinePullbackAdjunction.unit_isIso (g) (completePointOriginLine_rankOne K n h i m)

/-- The positive origin power is the direct image of the original marking tensor power. -/
def completePointOriginPowerDirectImageIso (m : ℕ) :
    originDivisorLine (W) m ≅ (pushforward (g)).obj (tensorPower (L) m) := by
  let _ := completePointOriginLine_unit_isIso K n h i m
  exact asIso ((pullbackPushforwardAdjunction (g)).unit.app (originDivisorLine (W) m)) ≪≫
    (pushforward (g)).mapIso (completePointOriginTensorLineIso K n h i m)

/-- The direct-image comparison is the adjoint of the original full-ideal line comparison. -/
theorem completePointOriginPowerDirectImageIso_hom (m : ℕ) :
    (completePointOriginPowerDirectImageIso K n h i m).hom =
      (pullbackPushforwardAdjunction (g)).homEquiv _ _
        (completePointOriginTensorLineIso K n h i m).hom := rfl

/-- Local sections of every origin power descend uniquely from the original polygon. -/
theorem completePointOriginPower_sections_bijective (m : ℕ)
    (V : (integralCurve (W)).Opens) :
    Function.Bijective ((completePointOriginPowerDirectImageIso K n h i m).hom.app V) :=
  ConcreteCategory.bijective_of_isIso _

/-- Removing the degree-one unitor keeps the original complete-base marking line. -/
def completePointOriginLineIso : (pullback (g)).obj (originDivisorLine (W) 1) ≅ (L) :=
  completePointOriginTensorLineIso K n h i 1 ≪≫ ModuleSheafTensor.rightUnitor (L)

end FLT.Mazur.PolygonInfinitesimalStages
