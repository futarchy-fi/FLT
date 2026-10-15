/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicCubicCoordinates

/-!
# The specialized cubic functions retain the original adic action map

The complete coordinate homomorphism specializes to the section map of the
actual original adic morphism. Both its action and target contraction are
retained on the full inverse-image patch.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i j : Fin n)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h m i j).toScheme.affineOpens)
local notation "W" => completeIdentityAdicAmbientTargetPatch K n h m i j U
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h m i j U
local notation "κ" => completeIdentityActionAdicChartSpaceMap K n h m i j ≫
  completeIdentityActionAdicLiftSpaceMap K n h m
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "C" k => completeIdentityCubicChartOpen K n h k
variable (k : Fin 3)
variable (hC : (completeIdentityAdicAmbientTargetPatch K n h m i j U).1 ≤
  completeIdentityCubicChartOpen K n h k)
include hC

/-- The entire original adic patch lies in the same actual cubic chart. -/
theorem completeIdentityAdicCubicPatch_le : (V).1 ≤ (κ) ⁻¹ᵁ (C k) := by
  rw [completeIdentityAdicAmbientPatch_preimage]
  exact fun _ hx ↦ hC hx

/-- The original adic action map into the actual affine cubic chart. -/
def completeIdentityAdicCubicChartMap : (V).1.toScheme ⟶ Spec (.of (Coordinate (E) k)) :=
  (κ).resLE (C k) (V).1 (completeIdentityAdicCubicPatch_le K n h m i j U k hC) ≫
    completeIdentityCubicActionChart K n h k
local notation "c" => completeIdentityAdicCubicChartMap K n h m i j U k hC
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)

/-- The specialized chart retains the original whole-input cubic action. -/
@[reassoc] theorem completeIdentityAdicCubicChartMap_action :
    (c) ≫ integralCurveChart (E) k =
      (V).1.ι ≫ (κ) ≫ pullback.fst (a) (g) ≫ (a) := by
  rw [completeIdentityAdicCubicChartMap, Category.assoc,
    completeIdentityCubicActionChart_inclusion, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι]
  simp only [Category.assoc]

/-- The same specialized chart retains the original target contraction. -/
@[reassoc] theorem completeIdentityAdicCubicChartMap_target :
    (c) ≫ integralCurveChart (E) k =
      (V).1.ι ≫ (κ) ≫ pullback.snd (a) (g) ≫ (g) := by
  rw [completeIdentityAdicCubicChartMap_action, pullback.condition]

/-- The complete-coordinate specialization is exactly this original morphism's section map. -/
theorem completeIdentityAdicCubicChartMap_functions :
    ((V).1.topIso.hom.hom.comp ((c).appTop.hom.comp
      (Scheme.ΓSpecIso (.of (Coordinate (E) k))).inv.hom)) =
      completeIdentityAdicCubicFunctions K n h m i j U k hC := by
  change ((Scheme.ΓSpecIso (.of (Coordinate (E) k))).inv ≫
    (c).appTop ≫ (V).1.topIso.hom).hom = _
  rw [completeIdentityAdicCubicChartMap, Scheme.Hom.comp_appTop]
  rw [show ((κ).resLE (C k) (V).1
    (completeIdentityAdicCubicPatch_le K n h m i j U k hC)).appTop =
      (C k).topIso.hom ≫ (κ).appLE (C k) (V).1
        (completeIdentityAdicCubicPatch_le K n h m i j U k hC) ≫ (V).1.topIso.inv from
    Scheme.Hom.resLE_app_top _ _]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change _ = ((Scheme.ΓSpecIso (.of (Coordinate (E) k))).inv ≫
    (completeIdentityCubicActionChart K n h k).appTop ≫ (C k).topIso.hom ≫
      (completeIdentityActionLiftSpace K n h).presheaf.map (homOfLE hC).op ≫
        (κ).appLE (W).1 (V).1
          (le_of_eq (completeIdentityAdicAmbientPatch_preimage K n h m i j U))).hom
  rw [Scheme.Hom.map_appLE]

end FLT.Mazur.PolygonInfinitesimalStages
