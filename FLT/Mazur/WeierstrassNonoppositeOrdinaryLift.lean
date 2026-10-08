/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOrdinaryDomainLift
public import FLT.Mazur.WeierstrassOrdinaryPointComparison

/-!
# Every nonopposite affine field pair lifts to an ordinary addition domain

The secant denominator is nonzero when abscissae differ. Otherwise the
nonopposite condition makes the second denominator nonzero. Localization
then supplies an actual chart point with precisely the two original inputs.
-/

@[expose] public noncomputable section

open WeierstrassCurve WeierstrassCurve.Projective
open CategoryTheory CartesianMonoidalCategory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable (W : WeierstrassCurve R)

/-- A nonopposite pair has an invertible ordinary denominator over a field. -/
theorem nonopposite_ordinary_denominator (f : AffineProduct W →ₐ[R] K)
    (h : ¬(f (productX₁ W) = f (productX₂ W) ∧
      f (productY₁ W) = (W.map (algebraMap R K)).toAffine.negY
        (f (productX₂ W)) (f (productY₂ W)))) :
    ∃ b : Bool, IsUnit (f (if b then tangentDenominator W else secantDenominator W)) := by
  by_cases hx : f (productX₁ W) = f (productX₂ W)
  · refine ⟨true, isUnit_iff_ne_zero.mpr ?_⟩
    intro hd
    apply h
    refine ⟨hx, ?_⟩
    simp only [ite_true, map_tangentDenominator] at hd
    simp only [Affine.negY, map_a₁, map_a₃]
    linear_combination hd
  · refine ⟨false, isUnit_iff_ne_zero.mpr ?_⟩
    simpa only [Bool.false_eq_true, ite_false, map_secantDenominator] using sub_ne_zero.mpr hx

/-- Both original affine algebra points lift together through one actual ordinary chart. -/
theorem exists_nonopposite_ordinary_lift (a c : Coordinate W 2 →ₐ[R] K)
    (h : ¬(a (coord W 2 0) = c (coord W 2 0) ∧
      a (coord W 2 1) = (W.map (algebraMap R K)).toAffine.negY
        (c (coord W 2 0)) (c (coord W 2 1)))) :
    ∃ (b : Bool) (f : additionChartRing W (ordinaryIndex b) →ₐ[R] K),
      f.comp (ordinaryInputLeft W b) = a ∧ f.comp (ordinaryInputRight W b) = c := by
  let p : AffineProduct W →ₐ[R] K := chartProductEvaluation W 2 2 a c
  have hl : p.comp (productLeft W) = a := chartProductEvaluation_left W 2 2 a c
  have hr : p.comp (productRight W) = c := chartProductEvaluation_right W 2 2 a c
  have hlc (i) : p (productLeft W (coord W 2 i)) = a (coord W 2 i) :=
    DFunLike.congr_fun hl _
  have hrc (i) : p (productRight W (coord W 2 i)) = c (coord W 2 i) :=
    DFunLike.congr_fun hr _
  obtain ⟨b, hb⟩ := nonopposite_ordinary_denominator W p (by
    simpa only [productX₁, productX₂, productY₁, productY₂, hlc, hrc] using h)
  refine ⟨b, ordinaryDomainLift W b p hb, ?_, ?_⟩
  · change (ordinaryDomainLift W b p hb).comp
      ((additionChartAlgRestriction W (ordinaryIndex b)).comp (productLeft W)) = a
    rw [← AlgHom.comp_assoc, ordinaryDomainLift_restriction, hl]
  · change (ordinaryDomainLift W b p hb).comp
      ((additionChartAlgRestriction W (ordinaryIndex b)).comp (productRight W)) = c
    rw [← AlgHom.comp_assoc, ordinaryDomainLift_restriction, hr]

/-- The comparison preserves addition for every nonopposite pair of affine algebra points. -/
theorem projectiveToIntegral_add_affineAlgHom (hΔ : IsUnit W.Δ)
    (a c : Coordinate W 2 →ₐ[R] K)
    (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular (a (coord W 2 0)) (a (coord W 2 1)))
    (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular (c (coord W 2 0)) (c (coord W 2 1)))
    (h : ¬(a (coord W 2 0) = c (coord W 2 0) ∧
      a (coord W 2 1) = (W.map (algebraMap R K)).toAffine.negY
        (c (coord W 2 0)) (c (coord W 2 1)))) :
    projectiveToIntegral W (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂)) =
      lift (projectiveToIntegral W (Point.fromAffine (.some _ _ h₁)))
        (projectiveToIntegral W (Point.fromAffine (.some _ _ h₂))) ≫
          integralCurveOverAddition W hΔ := by
  obtain ⟨b, f, ha, hc⟩ := exists_nonopposite_ordinary_lift W a c h
  have hf₁ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (f (ordinaryInputLeft W b (coord W 2 0))) (f (ordinaryInputLeft W b (coord W 2 1))) := by
    simpa only [← AlgHom.comp_apply, ha] using h₁
  have hf₂ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (f (ordinaryInputRight W b (coord W 2 0))) (f (ordinaryInputRight W b (coord W 2 1))) := by
    simpa only [← AlgHom.comp_apply, hc] using h₂
  simpa only [← AlgHom.comp_apply, ha, hc] using
    projectiveToIntegral_add_ordinary W b f hf₁ hf₂ hΔ

/-- The comparison preserves the sum of any nonopposite classical affine point pair. -/
theorem projectiveToIntegral_add_nonopposite (hΔ : IsUnit W.Δ) {x₁ x₂ y₁ y₂ : K}
    (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular x₂ y₂)
    (h : ¬(x₁ = x₂ ∧ y₁ = (W.map (algebraMap R K)).toAffine.negY x₂ y₂)) :
    projectiveToIntegral W (Point.fromAffine (.some _ _ h₁) + Point.fromAffine (.some _ _ h₂)) =
      lift (projectiveToIntegral W (Point.fromAffine (.some _ _ h₁)))
        (projectiveToIntegral W (Point.fromAffine (.some _ _ h₂))) ≫
          integralCurveOverAddition W hΔ := by
  let a := evaluation W 2 ![x₁, y₁, 1] ((equation_some ..).mpr h₁.left) rfl
  let c := evaluation W 2 ![x₂, y₂, 1] ((equation_some ..).mpr h₂.left) rfl
  have ha (i) : a (coord W 2 i) = ![x₁, y₁, 1] i := evaluation_coord W 2 _ _ _ i
  have hc (i) : c (coord W 2 i) = ![x₂, y₂, 1] i := evaluation_coord W 2 _ _ _ i
  have he := projectiveToIntegral_add_affineAlgHom W hΔ a c
    (by simpa only [ha, Matrix.cons_val_zero, Matrix.cons_val_one] using h₁)
    (by simpa only [hc, Matrix.cons_val_zero, Matrix.cons_val_one] using h₂)
    (by simpa only [ha, hc, Matrix.cons_val_zero, Matrix.cons_val_one] using h)
  simpa only [ha, hc, Matrix.cons_val_zero, Matrix.cons_val_one] using he

end FLT.Mazur.WeierstrassIntegralChart

