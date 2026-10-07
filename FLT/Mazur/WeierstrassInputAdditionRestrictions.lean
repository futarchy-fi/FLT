/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInputProductAddition

/-!
# Restrictions of the glued input-product addition morphisms

The descended maps retain the single glued affine law on the whole affine
input overlap and the polynomial law on its original output-Z open.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- On the whole affine overlap, Y-product addition is the glued affine law. -/
theorem yProductAdditionToCurve_affine :
    Spec.map (CommRingCat.ofHom (productOverlapRestriction W 1 1 2 2).toRingHom) ≫
        yProductAdditionToCurve W hΔ =
      affineInputOverlapMap W 1 1 ≫ affineAdditionToCurve W hΔ := by
  apply (affineOverlapAdditionCover W 1 1 hΔ).hom_ext
  intro i
  rw [← Category.assoc, ← transportedPolynomialDomainMap,
    ← yProductAdditionCover_affine_f, yProductCurveLocal_glued]
  exact (affineOverlapAdditionSpec_glued W hΔ 1 1 i).symm

/-- The polynomial output-Z law is the restriction of the glued Y-product morphism. -/
theorem yProductAdditionToCurve_polynomial :
    projectiveAdditionInclusion W 1 1 2 ≫ yProductAdditionToCurve W hΔ =
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W 1 1 2).toRingHom) ≫
        integralCurveChart W 2 := by
  simpa only [yProductAdditionCover_polynomial_f, yProductCurveLocal,
    yProductAdditionSpec, yProductAdditionOutput] using
    yProductCurveLocal_glued W hΔ ⟨.polynomial, PUnit.unit⟩

/-- The infinity-domain law is retained by Y-product descent. -/
theorem yProductAdditionToCurve_infinity :
    infinityAdditionInclusion W ≫ yProductAdditionToCurve W hΔ =
      infinityAdditionSpec W ≫ integralCurveChart W 1 := by
  simpa only [yProductAdditionCover_infinity_f, yProductCurveLocal,
    yProductAdditionSpec, yProductAdditionOutput] using
    yProductCurveLocal_glued W hΔ ⟨.infinity, PUnit.unit⟩

/-- Mixed-product addition restricts to the same single affine law. -/
theorem mixedProductAdditionToCurve_affine (j k : Fin 3)
    (hj : j = 1 ∨ j = 2) (hk : k = 1 ∨ k = 2) (ha : j = 2 ∨ k = 2) :
    Spec.map (CommRingCat.ofHom (productOverlapRestriction W j k 2 2).toRingHom) ≫
        mixedProductAdditionToCurve W hΔ j k hj hk ha =
      affineInputOverlapMap W j k ≫ affineAdditionToCurve W hΔ := by
  apply (affineOverlapAdditionCover W j k hΔ).hom_ext
  intro i
  rw [← Category.assoc, ← transportedPolynomialDomainMap,
    ← mixedProductAdditionCover_affine_f W hΔ j k hj hk ha, mixedProductCurveLocal_glued]
  exact (affineOverlapAdditionSpec_glued W hΔ j k i).symm

/-- Mixed-product descent retains the original polynomial output-Z law. -/
theorem mixedProductAdditionToCurve_polynomial (j k : Fin 3)
    (hj : j = 1 ∨ j = 2) (hk : k = 1 ∨ k = 2) (ha : j = 2 ∨ k = 2) :
    projectiveAdditionInclusion W j k 2 ≫ mixedProductAdditionToCurve W hΔ j k hj hk ha =
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k 2).toRingHom) ≫
        integralCurveChart W 2 := by
  simpa only [mixedProductAdditionCover_polynomial_f, mixedProductCurveLocal,
    mixedProductAdditionSpec, mixedProductAdditionOutput] using
    mixedProductCurveLocal_glued W hΔ j k hj hk ha ⟨false, PUnit.unit⟩

/-- Every input chart restricts to the same glued addition on its affine overlap. -/
theorem integralInputAdditionToCurve_affine (b c : Bool) :
    Spec.map (CommRingCat.ofHom (productOverlapRestriction W
      (productChartCoordinate b) (productChartCoordinate c) 2 2).toRingHom) ≫
        integralInputAdditionToCurve W hΔ b c =
      affineInputOverlapMap W (productChartCoordinate b) (productChartCoordinate c) ≫
        affineAdditionToCurve W hΔ := by
  cases b <;> cases c
  · exact mixedProductAdditionToCurve_affine W hΔ 2 2 (.inr rfl) (.inr rfl) (.inl rfl)
  · exact mixedProductAdditionToCurve_affine W hΔ 2 1 (.inr rfl) (.inl rfl) (.inl rfl)
  · exact mixedProductAdditionToCurve_affine W hΔ 1 2 (.inl rfl) (.inr rfl) (.inr rfl)
  · exact yProductAdditionToCurve_affine W hΔ

/-- Every input chart retains its polynomial output-Z formula. -/
theorem integralInputAdditionToCurve_polynomial (b c : Bool) :
    projectiveAdditionInclusion W (productChartCoordinate b) (productChartCoordinate c) 2 ≫
        integralInputAdditionToCurve W hΔ b c =
      Spec.map (CommRingCat.ofHom (projectiveAdditionChart W
        (productChartCoordinate b) (productChartCoordinate c) 2).toRingHom) ≫
          integralCurveChart W 2 := by
  cases b <;> cases c
  · exact mixedProductAdditionToCurve_polynomial W hΔ 2 2 (.inr rfl) (.inr rfl) (.inl rfl)
  · exact mixedProductAdditionToCurve_polynomial W hΔ 2 1 (.inr rfl) (.inl rfl) (.inl rfl)
  · exact mixedProductAdditionToCurve_polynomial W hΔ 1 2 (.inl rfl) (.inr rfl) (.inr rfl)
  · exact yProductAdditionToCurve_polynomial W hΔ

end FLT.Mazur.WeierstrassIntegralChart
