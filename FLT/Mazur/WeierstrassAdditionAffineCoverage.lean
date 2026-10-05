/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassVerticalAdditionCharts

/-!
# Field-valued coverage by the integral affine addition charts

For a nonsingular first point, either an ordinary slope denominator is nonzero
or a reciprocal denominator is nonzero with zero numerator. In the latter case
the field point lifts through both localizations of the reciprocal chart.
This covers affine pairs; it does not cover inputs at infinity or glue maps.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve WeierstrassIntegralAddition

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) (f : AffineProduct W →ₐ[R] K)

/-- A field-valued point lifts to the ratio chart when its denominator is nonzero. -/
def ratioLift (d : AffineProduct W) (hd : f d ≠ 0) : RatioChart W d →ₐ[R] K :=
  IsLocalization.Away.liftAlgHom d (isUnit_iff_ne_zero.mpr hd)

/-- The ratio-chart lift restricts to the original point. -/
@[simp] theorem ratioLift_restriction (d : AffineProduct W) (hd : f d ≠ 0)
    (a : AffineProduct W) :
    ratioLift W f d hd (ratioRestriction W d a) = f a :=
  IsLocalization.Away.lift_eq d (isUnit_iff_ne_zero.mpr hd) a

/-- A vanishing numerator gives reciprocal slope zero after lifting. -/
theorem ratioLift_slope_zero (d n : AffineProduct W) (hd : f d ≠ 0) (hn : f n = 0) :
    ratioLift W f d hd (ratioSlope W d n) = 0 := by
  have h := congrArg (ratioLift W f d hd) (ratioSlope_mul W d n)
  rw [map_mul, ratioLift_restriction, ratioLift_restriction, hn] at h
  exact (mul_eq_zero.mp h).resolve_right hd

/-- At a vanishing numerator the output y-coordinate is a unit, so no point is lost. -/
theorem ratioLift_output_isUnit (d n : AffineProduct W) (hd : f d ≠ 0) (hn : f n = 0) :
    IsUnit (ratioLift W f d hd
      (reciprocalCoordinates W (ratioRestriction W d) (ratioSlope W d n) 1)) := by
  have hm := ratioLift_slope_zero W f d n hd hn
  have hy : ratioLift W f d hd
      (reciprocalCoordinates W (ratioRestriction W d) (ratioSlope W d n) 1) = -1 := by
    simp only [reciprocalCoordinates, reciprocalXYZ, Matrix.cons_val_zero, Matrix.cons_val_one,
      reciprocalH, map_sub, map_add, map_mul, map_pow, map_neg, map_one,
      hm, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), mul_zero, add_zero,
      sub_zero, mul_one, neg_mul]
  rw [hy]
  exact isUnit_one.neg

/-- Lift an omitted ordinary-slope point through the entire reciprocal chart. -/
def reciprocalRatioLift (d n : AffineProduct W) (hd : f d ≠ 0) (hn : f n = 0) :
    ReciprocalTargetOpen W (ratioRestriction W d) (ratioSlope W d n) →ₐ[R] K :=
  IsLocalization.Away.liftAlgHom
    (reciprocalCoordinates W (ratioRestriction W d) (ratioSlope W d n) 1)
    (ratioLift_output_isUnit W f d n hd hn)

/-- The two-stage lift is a factorization of the original affine-product point. -/
@[simp] theorem reciprocalRatioLift_restriction (d n : AffineProduct W)
    (hd : f d ≠ 0) (hn : f n = 0) (a : AffineProduct W) :
    reciprocalRatioLift W f d n hd hn
      (reciprocalTargetRestriction W (ratioRestriction W d) (ratioSlope W d n)
        (ratioRestriction W d a)) = f a := by
  change IsLocalization.Away.lift _ (ratioLift_output_isUnit W f d n hd hn)
    (algebraMap _ _ (ratioRestriction W d a)) = f a
  rw [IsLocalization.Away.lift_eq]
  exact ratioLift_restriction W f d hd a

/-- Nonsingular affine pairs are covered by ordinary or zero-reciprocal slope charts. -/
theorem addition_denominators_cover
    (hs : (W.map (algebraMap R K)).toAffine.Nonsingular
      (f (productX₁ W)) (f (productY₁ W))) :
    f (secantDenominator W) ≠ 0 ∨ f (tangentDenominator W) ≠ 0 ∨
      (f (verticalSecantDenominator W) ≠ 0 ∧ f (secantDenominator W) = 0) ∨
      (f (tangentNumerator W) ≠ 0 ∧ f (tangentDenominator W) = 0) := by
  by_cases hx : f (secantDenominator W) = 0
  swap
  · exact Or.inl hx
  by_cases ht : f (tangentDenominator W) = 0
  swap
  · exact Or.inr (Or.inl ht)
  by_cases hy : f (verticalSecantDenominator W) = 0
  swap
  · exact Or.inr (Or.inr (Or.inl ⟨hy, hx⟩))
  refine Or.inr (Or.inr (Or.inr ⟨?_, ht⟩))
  intro hn
  rw [map_secantDenominator, sub_eq_zero] at hx
  rw [map_verticalSecantDenominator, sub_eq_zero] at hy
  rw [map_tangentDenominator] at ht
  rw [map_tangentNumerator] at hn
  have hs' := hs.2
  simp only [Affine.evalEval_polynomialX, Affine.evalEval_polynomialY, map_a₁, map_a₂,
    map_a₃, map_a₄] at hs'
  rcases hs' with hs' | hs'
  · apply hs'
    rw [← hx] at hn
    linear_combination -hn
  · apply hs'
    rw [← hx, ← hy] at ht
    linear_combination ht

/-- Good reduction supplies the nonsingularity needed for affine chart coverage. -/
theorem addition_denominators_cover_of_discriminant
    (hΔ : (W.map (algebraMap R K)).Δ ≠ 0) :
    f (secantDenominator W) ≠ 0 ∨ f (tangentDenominator W) ≠ 0 ∨
      (f (verticalSecantDenominator W) ≠ 0 ∧ f (secantDenominator W) = 0) ∨
      (f (tangentNumerator W) ≠ 0 ∧ f (tangentDenominator W) = 0) :=
  addition_denominators_cover W f
    ((Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (productLeft_equation W f))

end FLT.Mazur.WeierstrassIntegralChart
