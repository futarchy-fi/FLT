/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalChartSpecialization
public import FLT.Mazur.WeierstrassGlobalAffineSwap

/-!
# Reciprocal addition domains inside the actual curve product

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

/-- The original reciprocal domain as an open of the global product. -/
def reciprocalGlobalDomain (b : Bool) :
    Spec (additionChartRing W (reciprocalIndex b)) ⟶ integralCurveProduct W :=
  additionChartInclusion W (reciprocalIndex b) ≫ integralCurveProductChart W false false

instance reciprocalGlobalDomain_isOpenImmersion (b : Bool) :
    IsOpenImmersion (reciprocalGlobalDomain W b) := by
  unfold reciprocalGlobalDomain
  infer_instance

/-- The first global input is the original first affine input. -/
@[reassoc] theorem reciprocalGlobalDomain_fst (b : Bool) :
    reciprocalGlobalDomain W b ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (reciprocalInputLeft W b).toRingHom) ≫
        integralCurveChart W 2 := by
  rw [reciprocalGlobalDomain, Category.assoc, integralCurveProductChart_fst]
  change additionChartInclusion W (reciprocalIndex b) ≫
    Spec.map (CommRingCat.ofHom (productLeft W).toRingHom) ≫ _ = _
  rw [← Category.assoc, additionChartInclusion.eq_def, ← additionChartAlgRestriction_toRingHom,
    ← Spec.map_comp]
  rfl

/-- The second global input is the original second affine input. -/
@[reassoc] theorem reciprocalGlobalDomain_snd (b : Bool) :
    reciprocalGlobalDomain W b ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (reciprocalInputRight W b).toRingHom) ≫
        integralCurveChart W 2 := by
  rw [reciprocalGlobalDomain, Category.assoc, integralCurveProductChart_snd]
  change additionChartInclusion W (reciprocalIndex b) ≫
    Spec.map (CommRingCat.ofHom (productRight W).toRingHom) ≫ _ = _
  rw [← Category.assoc, additionChartInclusion.eq_def, ← additionChartAlgRestriction_toRingHom,
    ← Spec.map_comp]
  rfl

/-- Global addition restricts to the original normalized reciprocal formula. -/
@[reassoc] theorem reciprocalGlobalDomain_addition (hΔ : IsUnit W.Δ) (b : Bool) :
    reciprocalGlobalDomain W b ≫ integralCurveAddition W hΔ =
      Spec.map (CommRingCat.ofHom (reciprocalChartAddition W b).toRingHom) ≫
        integralCurveChart W 1 := by
  rw [reciprocalGlobalDomain, Category.assoc, integralCurveProductChart_affine_addition,
    additionCurveChart_glued]
  cases b <;> rfl

end FLT.Mazur.WeierstrassIntegralChart
