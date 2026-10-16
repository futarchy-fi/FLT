/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityCubicChartMaps
public import FLT.Mazur.PolygonCompletePointCubicChartRatios
public import FLT.Mazur.ModuleSectionRatioAlongMorphism

/-!
# Nonconstant cubic-action coordinates in the original complete relation

The action coordinates are exactly the target's normalized original pole
sections. Their full cubic equation holds before either graph or adic
specialization; no parameter power has been cancelled after reduction.
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
local notation "W" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "L" => completePointLine K n h (0 : Fin n)
local notation "T" => completePointProjectiveSections K n h (0 : Fin n)
local notation "U" j => sectionGeneratorOpen (tensorPower (L) 3) (T j)
local notation "C" j => completeIdentityCubicChartOpen K n h j
local notation "q" => pullback.snd (completeIdentityActionTarget K n h 0)
  (completePointToIntegralCubic K n h 0)

/-- The actual complete cubic action as a homomorphism on normalized coordinate functions. -/
def completeIdentityCubicFunctions (j : Fin 3) :
    Coordinate (W) j →+* Γ((C j).toScheme, ⊤) :=
  (completeIdentityCubicActionChart K n h j).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (Coordinate (W) j))).inv.hom
local notation "F" j => completeIdentityCubicFunctions K n h j

/-- Every nonconstant action coordinate is the retained target pole-section ratio. -/
theorem completeIdentityCubicFunctions_coordinate (j k : Fin 3) :
    (F j) (coord (W) j k) =
      ((q) ∣_ (U j)).appTop ((U j).topIso.inv
        (sectionRatioOn (tensorPower (L) 3) (T j) (U j) le_rfl (T k))) := by
  unfold completeIdentityCubicFunctions
  rw [completeIdentityCubicActionChart_eq_target, completeIdentityCubicTargetChart,
    Scheme.Hom.comp_appTop]
  change ((q) ∣_ (U j)).appTop
    ((completePointToCubicChart K n h 0 j).appTop _) = _
  rw [completePointToCubicChart_coordinate]

/-- Clear the actual cubic denominator in the original pulled-back line, before reduction. -/
theorem completeIdentityCubicFunctions_clear_denominator (j k : Fin 3) :
    (F j) (coord (W) j k) •
        pullGlobal ((C j).ι ≫ (q)) (tensorPower (L) 3) (T j) =
      pullGlobal ((C j).ι ≫ (q)) (tensorPower (L) 3) (T k) := by
  let f := (C j).ι ≫ (q)
  let M := tensorPower (L) 3
  have hj : ⊤ ≤ f ⁻¹ᵁ (U j) := by
    intro x _
    change (q) ((C j).ι x) ∈ U j
    exact x.property
  have he := congrArg (fun z ↦ ((Scheme.Modules.pullback f).obj M).presheaf.map
    (homOfLE hj).op (((pullbackPushforwardAdjunction f).unit.app M).app (U j) z))
    (sectionRatioOn_smul M (T j) (U j) le_rfl (T k))
  erw [Hom.app_smul, ((Scheme.Modules.pullback f).obj M).val.map_smul] at he
  change f.appLE (U j) ⊤ hj (sectionRatioOn M (T j) (U j) le_rfl (T k)) •
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hj).op
      (((pullbackPushforwardAdjunction f).unit.app M).app (U j)
        (M.presheaf.map (homOfLE le_top).op (T j))) = _ at he
  rw [pullGlobal_fromOpen, pullGlobal_fromOpen] at he
  rw [completeIdentityCubicFunctions_coordinate,
    openFactor_appTop f (U j) hj ((q) ∣_ (U j)) (morphismRestrict_ι _ _)]
  exact he

/-- The chosen coordinate is exactly one before specialization. -/
theorem completeIdentityCubicFunctions_self (j : Fin 3) : (F j) (coord (W) j j) = 1 := by
  rw [coord_self, map_one]

/-- The complete action coordinates satisfy the actual cubic with its original coefficients. -/
theorem completeIdentityCubicFunctions_equation (j : Fin 3) :
    ((W).map ((F j).comp (algebraMap _ (Coordinate (W) j)))).toProjective.Equation
      (fun k ↦ (F j) (coord (W) j k)) := by
  simpa only [WeierstrassCurve.map_map, Function.comp_def] using
    (coord_equation (W) j).map (F j)

end FLT.Mazur.PolygonInfinitesimalStages
