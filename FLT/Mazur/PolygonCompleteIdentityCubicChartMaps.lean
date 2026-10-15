/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionGraph
public import FLT.Mazur.PolygonCompletePointCubicChartSquare

/-!
# The original cubic action in complete affine cubic charts

The action and target contraction have the same actual affine chart map
on each complete generator open. This retains all three coordinate functions,
before imposing the smooth graph ideal or taking an adic quotient.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "Y" => completeIdentityActionLiftSpace K n h
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "W" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "L" => completePointLine K n h (0 : Fin n)
local notation "T" => completePointProjectiveSections K n h (0 : Fin n)
local notation "q" => pullback.snd (a) (g)
local notation "s" => pullback.fst (a) (g)
local notation "U" j => sectionGeneratorOpen (tensorPower (L) 3) (T j)

/-- The complete ambient open where the original target has its j-th cubic coordinate. -/
abbrev completeIdentityCubicChartOpen (j : Fin 3) : (Y).Opens := (q) ⁻¹ᵁ (U j)
local notation "C" j => completeIdentityCubicChartOpen K n h j

/-- The original target contraction, with its actual normalized section coordinates. -/
def completeIdentityCubicTargetChart (j : Fin 3) :
    (C j).toScheme ⟶ Spec (.of (Coordinate (W) j)) :=
  ((q) ∣_ (U j)) ≫ completePointToCubicChart K n h 0 j

/-- The complete target chart retains the original target map into the cubic. -/
@[reassoc] theorem completeIdentityCubicTargetChart_inclusion (j : Fin 3) :
    completeIdentityCubicTargetChart K n h j ≫ integralCurveChart (W) j =
      (C j).ι ≫ (q) ≫ (g) := by
  rw [completeIdentityCubicTargetChart, Category.assoc,
    completePointToCubicChart_inclusion]
  change ((q) ∣_ (U j)) ≫ (U j).ι ≫ (g) = _
  rw [morphismRestrict_ι_assoc]

/-- The actual cubic action lands in the same affine cubic chart on this entire open. -/
theorem completeIdentityCubicAction_chart_range (j : Fin 3) :
    Set.range ((C j).ι ≫ (s) ≫ (a)) ⊆ Set.range (integralCurveChart (W) j) := by
  rw [pullback.condition, ← completeIdentityCubicTargetChart_inclusion]
  rintro _ ⟨x, rfl⟩
  exact ⟨completeIdentityCubicTargetChart K n h j x, (Scheme.Hom.comp_apply _ _ x).symm⟩

/-- The unchanged cubic action in affine coordinates, without a generic-fiber restriction. -/
def completeIdentityCubicActionChart (j : Fin 3) :
    (C j).toScheme ⟶ Spec (.of (Coordinate (W) j)) :=
  IsOpenImmersion.lift (integralCurveChart (W) j) ((C j).ι ≫ (s) ≫ (a))
    (completeIdentityCubicAction_chart_range K n h j)

/-- The action chart map retains the original whole-input cubic action. -/
@[reassoc] theorem completeIdentityCubicActionChart_inclusion (j : Fin 3) :
    completeIdentityCubicActionChart K n h j ≫ integralCurveChart (W) j =
      (C j).ι ≫ (s) ≫ (a) := IsOpenImmersion.lift_fac _ _ _

/-- All original nonconstant cubic coordinates agree in the complete ambient relation. -/
theorem completeIdentityCubicActionChart_eq_target (j : Fin 3) :
    completeIdentityCubicActionChart K n h j = completeIdentityCubicTargetChart K n h j := by
  apply (cancel_mono (integralCurveChart (W) j)).mp
  rw [completeIdentityCubicActionChart_inclusion, completeIdentityCubicTargetChart_inclusion,
    pullback.condition]

/-- These actual cubic coordinate opens cover the entire complete ambient relation. -/
theorem completeIdentityCubicChartOpen_cover : (⨆ j, C j) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, completePointProjectiveSections_cover]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
