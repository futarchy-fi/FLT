/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryChartSpecialization
public import FLT.Mazur.WeierstrassGlobalAffineSwap

/-!
# Ordinary addition domains inside the actual curve product

These are the existing secant and tangent opens with their original input
projections. Global addition restricts to their already constructed output maps.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The original ordinary domain as an open of the global product. -/
def ordinaryGlobalDomain (b : Bool) :
    Spec (additionChartRing W (ordinaryIndex b)) ⟶ integralCurveProduct W :=
  additionChartInclusion W (ordinaryIndex b) ≫ integralCurveProductChart W false false

instance ordinaryGlobalDomain_isOpenImmersion (b : Bool) :
    IsOpenImmersion (ordinaryGlobalDomain W b) := by
  unfold ordinaryGlobalDomain
  infer_instance

/-- The first global input is the original first affine input. -/
@[reassoc] theorem ordinaryGlobalDomain_fst (b : Bool) :
    ordinaryGlobalDomain W b ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (ordinaryInputLeft W b).toRingHom) ≫
        integralCurveChart W 2 := by
  rw [ordinaryGlobalDomain, Category.assoc, integralCurveProductChart_fst]
  change additionChartInclusion W (ordinaryIndex b) ≫
    Spec.map (CommRingCat.ofHom (productLeft W).toRingHom) ≫ _ = _
  rw [← Category.assoc, additionChartInclusion.eq_def, ← additionChartAlgRestriction_toRingHom,
    ← Spec.map_comp]
  rfl

/-- The second global input is the original second affine input. -/
@[reassoc] theorem ordinaryGlobalDomain_snd (b : Bool) :
    ordinaryGlobalDomain W b ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (ordinaryInputRight W b).toRingHom) ≫
        integralCurveChart W 2 := by
  rw [ordinaryGlobalDomain, Category.assoc, integralCurveProductChart_snd]
  change additionChartInclusion W (ordinaryIndex b) ≫
    Spec.map (CommRingCat.ofHom (productRight W).toRingHom) ≫ _ = _
  rw [← Category.assoc, additionChartInclusion.eq_def, ← additionChartAlgRestriction_toRingHom,
    ← Spec.map_comp]
  rfl

/-- The actual global addition on an ordinary domain is its original affine formula. -/
@[reassoc] theorem ordinaryGlobalDomain_addition (hΔ : IsUnit W.Δ) (b : Bool) :
    ordinaryGlobalDomain W b ≫ integralCurveAddition W hΔ =
      Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom) ≫
        integralCurveChart W 2 := by
  rw [ordinaryGlobalDomain, Category.assoc, integralCurveProductChart_affine_addition,
    additionCurveChart_glued]
  cases b <;> rfl

end FLT.Mazur.WeierstrassIntegralChart
