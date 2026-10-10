/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCrossInputAdditionComparison

/-!
# Global regular addition on the integral cubic in good reduction

Addition agrees across the four actual input charts. The affine and polynomial
opens cover every mixed input product, so their established comparisons suffice
for global descent. Every original local formula is recovered by restriction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- If the second input presentation has an affine factor, its two opens prove compatibility. -/
theorem integralInputAdditionToCurve_mixed_commonScheme (b c d e : Bool)
    (ha : productChartCoordinate d = 2 ∨ productChartCoordinate e = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))))
    (g : X ⟶ Spec (.of (ChartProduct W (productChartCoordinate d) (productChartCoordinate e))))
    (h : f ≫ integralCurveProductChart W b c = g ≫ integralCurveProductChart W d e) :
    f ≫ integralInputAdditionToCurve W hΔ b c =
      g ≫ integralInputAdditionToCurve W hΔ d e := by
  have hd : productChartCoordinate d = 1 ∨ productChartCoordinate d = 2 := by
    cases d <;> simp [productChartCoordinate]
  have he : productChartCoordinate e = 1 ∨ productChartCoordinate e = 2 := by
    cases e <;> simp [productChartCoordinate]
  let C := mixedProductOpenCover W (productChartCoordinate d) (productChartCoordinate e) hd he ha
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro i
  let p := (C.pullback₁ g).f i
  let q := Scheme.Cover.pullbackHom C g i
  have hi : p ≫ g = q ≫ C.f i := (Scheme.Cover.pullbackHom_map C g i).symm
  have hg : (p ≫ f) ≫ integralCurveProductChart W b c =
      (q ≫ C.f i) ≫ integralCurveProductChart W d e := by
    rw [Category.assoc, h, ← Category.assoc, hi]
  change p ≫ (f ≫ integralInputAdditionToCurve W hΔ b c) =
    p ≫ (g ≫ integralInputAdditionToCurve W hΔ d e)
  rw [← Category.assoc p g, hi, Category.assoc]
  cases i
  · change p ≫ (f ≫ integralInputAdditionToCurve W hΔ b c) =
      q ≫ projectiveAdditionInclusion W (productChartCoordinate d) (productChartCoordinate e) 2 ≫
        integralInputAdditionToCurve W hΔ d e
    rw [integralInputAdditionToCurve_polynomial]
    change (p ≫ f) ≫ integralCurveProductChart W b c =
      (q ≫ projectiveAdditionInclusion W (productChartCoordinate d) (productChartCoordinate e) 2) ≫
        integralCurveProductChart W d e at hg
    exact (Category.assoc _ _ _).symm.trans
      (integralInputAdditionToCurve_commonPolynomial W hΔ b c d e (p ≫ f) q
        (by simpa only [Category.assoc] using hg))
  · change p ≫ (f ≫ integralInputAdditionToCurve W hΔ b c) =
      q ≫ Spec.map (CommRingCat.ofHom (productOverlapRestriction W
        (productChartCoordinate d) (productChartCoordinate e) 2 2).toRingHom) ≫
          integralInputAdditionToCurve W hΔ d e
    rw [integralInputAdditionToCurve_affine]
    have hn := congrArg (fun t => q ≫ t) (integralProductOverlap_condition W d e false false)
    change q ≫ C.f true ≫ integralCurveProductChart W d e =
      q ≫ affineInputOverlapMap W (productChartCoordinate d) (productChartCoordinate e) ≫
        integralCurveProductChart W false false at hn
    have hh : (p ≫ f) ≫ integralCurveProductChart W b c =
        (q ≫ affineInputOverlapMap W (productChartCoordinate d) (productChartCoordinate e)) ≫
          integralCurveProductChart W false false :=
      hg.trans (by simpa only [Category.assoc] using hn)
    simpa only [Category.assoc] using
      integralInputAdditionToCurve_commonAffine W hΔ b c (p ≫ f) _ hh

/-- The four descended addition morphisms agree whenever their global inputs agree. -/
theorem integralInputAdditionToCurve_commonScheme (b c d e : Bool) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))))
    (g : X ⟶ Spec (.of (ChartProduct W (productChartCoordinate d) (productChartCoordinate e))))
    (h : f ≫ integralCurveProductChart W b c = g ≫ integralCurveProductChart W d e) :
    f ≫ integralInputAdditionToCurve W hΔ b c =
      g ≫ integralInputAdditionToCurve W hΔ d e := by
  cases d <;> cases e
  · exact integralInputAdditionToCurve_mixed_commonScheme W hΔ b c false false (.inl rfl) f g h
  · exact integralInputAdditionToCurve_mixed_commonScheme W hΔ b c false true (.inl rfl) f g h
  · exact integralInputAdditionToCurve_mixed_commonScheme W hΔ b c true false (.inr rfl) f g h
  · cases b <;> cases c
    · exact (integralInputAdditionToCurve_mixed_commonScheme W hΔ true true false false
        (.inl rfl) g f h.symm).symm
    · exact (integralInputAdditionToCurve_mixed_commonScheme W hΔ true true false true
        (.inl rfl) g f h.symm).symm
    · exact (integralInputAdditionToCurve_mixed_commonScheme W hΔ true true true false
        (.inr rfl) g f h.symm).symm
    · have hf : f = g := (cancel_mono (integralCurveProductChart W true true)).mp h
      exact congrArg (fun t => t ≫ integralInputAdditionToCurve W hΔ true true) hf

/-- Global regular addition on the actual integral cubic product in good reduction. -/
def integralCurveAddition : integralCurveProduct W ⟶ integralCurve W :=
  (integralCurveProductCover W).glueMorphisms
    (fun p => integralInputAdditionToCurve W hΔ p.1 p.2)
    (fun p q => integralInputAdditionToCurve_commonScheme W hΔ p.1 p.2 q.1 q.2
      _ _ pullback.condition)

/-- Restricting global addition to an input chart recovers its descended law. -/
theorem integralCurveProductChart_addition (b c : Bool) :
    integralCurveProductChart W b c ≫ integralCurveAddition W hΔ =
      integralInputAdditionToCurve W hΔ b c :=
  (integralCurveProductCover W).ι_glueMorphisms _ _ (b, c)

/-- Every original member of the full addition cover recovers its original local formula. -/
theorem integralCurveAdditionLocal_glued (i : (integralCurveAdditionCover W hΔ).I₀) :
    (integralCurveAdditionCover W hΔ).f i ≫ integralCurveAddition W hΔ =
      integralCurveAdditionLocal W hΔ i := by
  change ((integralInputAdditionCover W hΔ i.1.1 i.1.2).f i.2 ≫
    integralCurveProductChart W i.1.1 i.1.2) ≫ integralCurveAddition W hΔ = _
  rw [Category.assoc, integralCurveProductChart_addition, integralInputAdditionLocal_glued]
  rfl

/-- The full local addition cover satisfies the actual pullback compatibility equation. -/
theorem integralCurveAdditionLocal_compatibility (i j : (integralCurveAdditionCover W hΔ).I₀) :
    pullback.fst ((integralCurveAdditionCover W hΔ).f i) ((integralCurveAdditionCover W hΔ).f j) ≫
        integralCurveAdditionLocal W hΔ i =
      pullback.snd ((integralCurveAdditionCover W hΔ).f i) ((integralCurveAdditionCover W hΔ).f j) ≫
        integralCurveAdditionLocal W hΔ j := by
  rw [← integralCurveAdditionLocal_glued, ← integralCurveAdditionLocal_glued,
    ← Category.assoc, pullback.condition, Category.assoc]

end FLT.Mazur.WeierstrassIntegralChart
