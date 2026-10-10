/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalNegation
public import FLT.Mazur.WeierstrassInfinityNegationInvolution

/-!
# Global negation is an involutive automorphism

The affine chart and the invariant infinity neighborhood cover the cubic.
The algebra involutions on these actual domains prove that the constructed
global regular negation is its own inverse as a scheme morphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The normalized infinity formula factors through its own invariant neighborhood. -/
theorem infinityNegationEnd_spec_restriction :
    Spec.map (CommRingCat.ofHom (infinityNegationEnd W).toRingHom) ≫
      infinityNegationInclusion W =
        Spec.map (CommRingCat.ofHom (infinityNegationChart W).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (infinityNegationEnd_restriction W)

/-- Applying negation twice is the identity on the affine chart. -/
theorem integralCurveNegation_twice_affine :
    integralCurveChart W 2 ≫ integralCurveNegation W ≫ integralCurveNegation W =
      integralCurveChart W 2 := by
  rw [← Category.assoc, integralCurveChart_negation_affine, Category.assoc,
    integralCurveChart_negation_affine, ← Category.assoc, ← Spec.map_comp]
  have h := congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (affineNegation_comp W)
  change Spec.map (CommRingCat.ofHom
    ((affineNegation W).comp (affineNegation W)).toRingHom) ≫ integralCurveChart W 2 = _
  rw [h]
  simp

/-- Applying negation twice restores the whole infinity neighborhood. -/
theorem integralCurveNegation_twice_infinity :
    infinityNegationInclusion W ≫ integralCurveChart W 1 ≫
        integralCurveNegation W ≫ integralCurveNegation W =
      infinityNegationInclusion W ≫ integralCurveChart W 1 := by
  rw [← Category.assoc (integralCurveChart W 1), ← Category.assoc,
    integralCurveChart_negation_infinity, ← infinityNegationEnd_spec_restriction,
    Category.assoc, Category.assoc, integralCurveChart_negation_infinity,
    ← Category.assoc, ← Spec.map_comp]
  have h := congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (infinityNegationEnd_chart W)
  change Spec.map (CommRingCat.ofHom
    ((infinityNegationEnd W).comp (infinityNegationChart W)).toRingHom) ≫
      integralCurveChart W 1 = _
  rw [h]
  rfl

/-- The actual global regular negation is an involution on the whole integral cubic. -/
theorem integralCurveNegation_comp :
    integralCurveNegation W ≫ integralCurveNegation W = 𝟙 (integralCurve W) := by
  apply (negationCover W).hom_ext
  intro b
  cases b
  · change integralCurveChart W 2 ≫ _ = integralCurveChart W 2 ≫ 𝟙 _
    rw [integralCurveNegation_twice_affine, Category.comp_id]
  · change (infinityNegationInclusion W ≫ integralCurveChart W 1) ≫ _ =
      (infinityNegationInclusion W ≫ integralCurveChart W 1) ≫ 𝟙 _
    rw [Category.assoc, integralCurveNegation_twice_infinity, Category.comp_id]

/-- Negation is an actual automorphism of the glued scheme over arbitrary coefficients. -/
def integralCurveNegationIso : integralCurve W ≅ integralCurve W where
  hom := integralCurveNegation W
  inv := integralCurveNegation W
  hom_inv_id := integralCurveNegation_comp W
  inv_hom_id := integralCurveNegation_comp W

end FLT.Mazur.WeierstrassIntegralChart
