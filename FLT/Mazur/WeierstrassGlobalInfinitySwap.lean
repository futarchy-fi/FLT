/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalAffineSwap
public import FLT.Mazur.WeierstrassSwappedInfinitySchemes

/-!
# Global input symmetry on the infinity domain

Pull the genuine Y-product cover back along the reversed infinity-domain input.
On its affine and polynomial members symmetry is already proved; on its infinity
member the actual reversed-input tensor comparison identifies the outputs.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Restriction of global addition to the original infinity domain. -/
theorem integralCurveAddition_infinity :
    infinityAdditionInclusion W ≫ integralCurveProductChart W true true ≫
        integralCurveAddition W hΔ =
      infinityAdditionSpec W ≫ integralCurveChart W 1 := by
  rw [integralCurveProductChart_addition]
  exact yProductAdditionToCurve_infinity W hΔ

/-- Global addition outputs agree on the actual reversed infinity intersections. -/
theorem integralCurveAddition_infinity_common {X : Scheme.{u}}
    (f g : X ⟶ Spec (.of (InfinityAdditionOpen W)))
    (h : f ≫ infinityAdditionInclusion W =
      g ≫ infinityAdditionInclusion W ≫ infinityInputSwap W) :
    f ≫ infinityAdditionInclusion W ≫ integralCurveProductChart W true true ≫
        integralCurveAddition W hΔ =
      g ≫ infinityAdditionInclusion W ≫ integralCurveProductChart W true true ≫
        integralCurveAddition W hΔ := by
  rw [integralCurveAddition_infinity]
  simpa only [Category.assoc] using
    congrArg (fun t => t ≫ integralCurveChart W 1) (infinityAddition_swap_commonScheme W f g h)

/-- Global addition is symmetric on the entire original infinity domain. -/
theorem integralCurveAddition_swap_infinity :
    infinityAdditionInclusion W ≫ integralCurveProductChart W true true ≫
        integralCurveSwap W ≫ integralCurveAddition W hΔ =
      infinityAdditionInclusion W ≫ integralCurveProductChart W true true ≫
        integralCurveAddition W hΔ := by
  let C := yProductOpenCover W
  let v := infinityAdditionInclusion W ≫ infinityInputSwap W
  apply Scheme.Cover.hom_ext (C.pullback₁ v)
  intro i
  let p := (C.pullback₁ v).f i
  let q := Scheme.Cover.pullbackHom C v i
  have hi : q ≫ C.f i = p ≫ infinityAdditionInclusion W ≫ infinityInputSwap W :=
    Scheme.Cover.pullbackHom_map C v i
  have hs : infinityInputSwap W ≫ integralCurveProductChart W true true =
      integralCurveProductChart W true true ≫ integralCurveSwap W :=
    (integralCurveProductChart_swap W true true).symm
  have hinput : q ≫ C.f i ≫ integralCurveProductChart W true true =
      p ≫ infinityAdditionInclusion W ≫ integralCurveProductChart W true true ≫
        integralCurveSwap W := by
    rw [← Category.assoc q, hi, Category.assoc, Category.assoc, hs]
  change p ≫ (infinityAdditionInclusion W ≫ integralCurveProductChart W true true ≫
      integralCurveSwap W ≫ integralCurveAddition W hΔ) =
    p ≫ (infinityAdditionInclusion W ≫ integralCurveProductChart W true true ≫
      integralCurveAddition W hΔ)
  have hss : integralCurveSwap W ≫ integralCurveSwap W ≫ integralCurveAddition W hΔ =
      integralCurveAddition W hΔ := by
    rw [← Category.assoc, integralCurveSwap_swap, Category.id_comp]
  cases i
  · have he := congrArg (fun t => q ≫ t)
      (integralCurveAddition_swap_affineOverlap W hΔ true true)
    change q ≫ C.f .affine ≫ integralCurveProductChart W true true ≫
        integralCurveSwap W ≫ integralCurveAddition W hΔ =
      q ≫ C.f .affine ≫ integralCurveProductChart W true true ≫
        integralCurveAddition W hΔ at he
    have hh := congrArg (fun t => t ≫ integralCurveSwap W ≫ integralCurveAddition W hΔ)
      hinput
    have hk := congrArg (fun t => t ≫ integralCurveAddition W hΔ) hinput
    simp only [Category.assoc, hss] at hh hk
    exact hk.symm.trans (he.symm.trans hh)
  · have he := congrArg (fun t => q ≫ t)
      (integralCurveAddition_swap_polynomial W hΔ true true)
    change q ≫ C.f .polynomial ≫ integralCurveProductChart W true true ≫
        integralCurveSwap W ≫ integralCurveAddition W hΔ =
      q ≫ C.f .polynomial ≫ integralCurveProductChart W true true ≫
        integralCurveAddition W hΔ at he
    have hh := congrArg (fun t => t ≫ integralCurveSwap W ≫ integralCurveAddition W hΔ)
      hinput
    have hk := congrArg (fun t => t ≫ integralCurveAddition W hΔ) hinput
    simp only [Category.assoc, hss] at hh hk
    exact hk.symm.trans (he.symm.trans hh)
  · have hk := congrArg (fun t => t ≫ integralCurveAddition W hΔ) hinput
    simp only [Category.assoc] at hk
    exact hk.symm.trans (integralCurveAddition_infinity_common W hΔ q p hi)

end FLT.Mazur.WeierstrassIntegralChart
