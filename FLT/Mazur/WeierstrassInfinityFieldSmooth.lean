/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothProductFieldPoints
public import FLT.Mazur.WeierstrassProductBoundaryPoints
public import FLT.Mazur.WeierstrassSmoothZeroSection

/-!
# Smooth field-valued outputs of the original infinity law

The simultaneous affine overlap, mixed boundary pairs, and the infinity pair
exhaust field-valued inputs. Comparing the original formulas on these three
parts proves smoothness without a discriminant hypothesis.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) (f : InfinityAdditionOpen W →ₐ[R] K)

/-- At a pair of boundary points, the original infinity law outputs the zero section. -/
theorem infinityFieldPoint_boundary
    (hl : f (infinityAdditionRestriction W (chartProductLeft W 1 1 (coord W 1 2))) = 0)
    (hr : f (infinityAdditionRestriction W (chartProductRight W 1 1 (coord W 1 2))) = 0) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ infinityAdditionSpec W ≫
        integralCurveChart W 1 =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ integralCurveZero W := by
  have hi : Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ infinityPairSectionSpec W := by
    apply (cancel_mono (infinityAdditionInclusion W)).mp
    rw [Category.assoc, infinityPairSectionSpec_inclusion]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun a : ChartProduct W 1 1 →ₐ[R] K =>
      Spec.map (CommRingCat.ofHom a.toRingHom))
      (product_boundary_pair_eq W (f.comp (infinityAdditionRestriction W)) hl hr)
  rw [hi, Category.assoc, ← Category.assoc (infinityPairSectionSpec W),
    infinityPairSectionSpec_addition]
  rfl

/-- The polynomial chart proves smoothness whenever its output Z coordinate is nonzero. -/
theorem infinityFieldPoint_range_smooth_of_polynomial
    (hl : (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ infinityAdditionRestriction W ∘ chartProductLeft W 1 1 ∘ coord W 1))
    (hr : (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ infinityAdditionRestriction W ∘ chartProductRight W 1 1 ∘ coord W 1))
    (hz : f (infinityAdditionRestriction W (chartProductAdditionCoordinates W 1 1 2)) ≠ 0) :
    Set.range (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ infinityAdditionSpec W ≫
      integralCurveChart W 1) ⊆ integralSmoothOpen W := by
  let a := f.comp (infinityAdditionRestriction W)
  let g : AdditionOutputOpen W 1 1 2 →ₐ[R] K :=
    IsLocalization.Away.liftAlgHom (f := a) (chartProductAdditionCoordinates W 1 1 2)
      (show IsUnit (a (chartProductAdditionCoordinates W 1 1 2)) from
        isUnit_iff_ne_zero.mpr hz)
  have hg : g.comp (additionOutputRestriction W 1 1 2) = a := by
    apply AlgHom.ext
    intro x
    change g (algebraMap (ChartProduct W 1 1) (AdditionOutputOpen W 1 1 2) x) = a x
    simp only [g, IsLocalization.Away.liftAlgHom_apply]
    exact IsLocalization.Away.lift_eq (g := a.toRingHom) (chartProductAdditionCoordinates W 1 1 2)
      (show IsUnit (a (chartProductAdditionCoordinates W 1 1 2)) from
        isUnit_iff_ne_zero.mpr hz) x
  have hi : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ infinityAdditionInclusion W =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ projectiveAdditionInclusion W 1 1 2 := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun b : ChartProduct W 1 1 →ₐ[R] K =>
      Spec.map (CommRingCat.ofHom b.toRingHom)) hg.symm
  rw [infinityPolynomial_curve_eq W 2 _ _ hi]
  have hgl : (W.map (algebraMap R K)).toProjective.Nonsingular
      (g ∘ additionOutputRestriction W 1 1 2 ∘ chartProductLeft W 1 1 ∘ coord W 1) := by
    change (W.map (algebraMap R K)).toProjective.Nonsingular
      ((g.comp (additionOutputRestriction W 1 1 2)) ∘ chartProductLeft W 1 1 ∘ coord W 1)
    rw [hg]
    exact hl
  have hgr : (W.map (algebraMap R K)).toProjective.Nonsingular
      (g ∘ additionOutputRestriction W 1 1 2 ∘ chartProductRight W 1 1 ∘ coord W 1) := by
    change (W.map (algebraMap R K)).toProjective.Nonsingular
      ((g.comp (additionOutputRestriction W 1 1 2)) ∘ chartProductRight W 1 1 ∘ coord W 1)
    rw [hg]
    exact hr
  have hs := polynomialFieldPoint_range_smooth W 1 1 2 g hgl hgr
  change Set.range (Spec.map (CommRingCat.ofHom
    (g.toRingHom.comp (projectiveAdditionChart W 1 1 2).toRingHom)) ≫ _) ⊆ _ at hs
  rwa [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] at hs

/-- Every smooth input of the infinity formula has smooth output over an arbitrary field. -/
theorem infinityFieldPoint_range_smooth
    (hl : (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ infinityAdditionRestriction W ∘ chartProductLeft W 1 1 ∘ coord W 1))
    (hr : (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ infinityAdditionRestriction W ∘ chartProductRight W 1 1 ∘ coord W 1)) :
    Set.range (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ infinityAdditionSpec W ≫
      integralCurveChart W 1) ⊆ integralSmoothOpen W := by
  let a := f.comp (infinityAdditionRestriction W)
  by_cases hzl : a (chartProductLeft W 1 1 (coord W 1 2)) = 0
  · by_cases hzr : a (chartProductRight W 1 1 (coord W 1 2)) = 0
    · rw [infinityFieldPoint_boundary W f hzl hzr]
      rintro _ ⟨p, rfl⟩
      exact integralCurveZero_range_smooth W ⟨_, rfl⟩
    · exact infinityFieldPoint_range_smooth_of_polynomial W f hl hr
        (product_add_left_boundary_z_ne_zero W 1 a hzl hzr)
  · by_cases hzr : a (chartProductRight W 1 1 (coord W 1 2)) = 0
    · exact infinityFieldPoint_range_smooth_of_polynomial W f hl hr
        (product_add_right_boundary_z_ne_zero W 1 a hzl hzr)
    · let g := productOverlapLift W 1 1 2 2 a
        (isUnit_iff_ne_zero.mpr hzl) (isUnit_iff_ne_zero.mpr hzr)
      have hg : g.comp (productOverlapRestriction W 1 1 2 2) = a :=
        productOverlapLift_restriction W 1 1 2 2 a _ _
      have hi : Spec.map (CommRingCat.ofHom g.toRingHom) ≫
          integralProductOverlapFst W true true false false =
            Spec.map (CommRingCat.ofHom f.toRingHom) ≫ infinityAdditionInclusion W := by
        change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp, ← Spec.map_comp]
        exact congrArg (fun b : ChartProduct W 1 1 →ₐ[R] K =>
          Spec.map (CommRingCat.ofHom b.toRingHom)) hg
      have hs : Set.range (Spec.map (CommRingCat.ofHom g.toRingHom) ≫
          integralProductOverlapFst W true true false false) ⊆
            smoothProductChartOpen W true true := by
        rw [hi]
        change Set.range (Spec.map _ ≫ Spec.map _) ⊆ _
        rw [← Spec.map_comp]
        exact productFieldPoint_range_smooth W true true a hl hr
      let l := smoothAffineOverlapLift W true true
        (Spec.map (CommRingCat.ofHom g.toRingHom)) hs
      have he := smoothAffineOverlap_infinity W l
        (Spec.map (CommRingCat.ofHom f.toRingHom))
        ((smoothAffineOverlapLift_input W true true _ hs).trans hi)
      rw [← he]
      rintro _ ⟨p, rfl⟩
      exact (smoothAffineOverlapAddition W true true (l p)).property

/-- The output's normalized coordinates are classically nonsingular. -/
theorem infinityFieldPoint_nonsingular
    (hl : (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ infinityAdditionRestriction W ∘ chartProductLeft W 1 1 ∘ coord W 1))
    (hr : (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ infinityAdditionRestriction W ∘ chartProductRight W 1 1 ∘ coord W 1)) :
    (W.map (algebraMap R K)).toProjective.Nonsingular
      (f ∘ infinityAdditionChart W ∘ coord W 1) := by
  apply chartFieldPoint_nonsingular_of_smooth W 1 (f.comp (infinityAdditionChart W))
  change Set.range (Spec.map (CommRingCat.ofHom
    (f.toRingHom.comp (infinityAdditionChart W).toRingHom)) ≫ _) ⊆ _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  exact infinityFieldPoint_range_smooth W f hl hr

end FLT.Mazur.WeierstrassIntegralChart
