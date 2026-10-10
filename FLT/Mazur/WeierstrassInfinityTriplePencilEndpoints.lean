/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleCrossDenominators
public import FLT.Mazur.WeierstrassInfinityTripleLineResidual

/-!
# Endpoint constraints from all three actual pencils

These scalar equations connect the inner and outer point factors to the cross
denominators with certified unit combinations. Evaluating the pencil identities
retains their divided-cubic information when inputs coincide.
-/

@[expose] public noncomputable section

open AlgebraicGeometry Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- Evaluation of the genuine pencil retains both of its line values. -/
theorem infinityTriplePencilPolynomial_eval (i : Fin 7) (j k : Fin 4)
    (t : Γ(InfinityTripleFull W hΔ, ⊤)) :
    let A := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ i
    let z := infinityTripleScalarZ W hΔ i
    let l := infinityTripleScalarSlope W hΔ j
    let m := infinityTripleScalarSlope W hΔ k
    (infinityTriplePencilPolynomial W hΔ i j k).eval t =
      (l - m) * infinitySlopeDenominator A t (z + l * (t - x)) (z + m * (t - x)) := by
  simp only [infinityTriplePencilPolynomial, infinitySlopeDenominator,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    eval_mul, eval_sub, eval_add, eval_pow, eval_C, eval_X, eval_one]

/-- The inner endpoint equation uses the forward cross denominator of the last inner law. -/
theorem infinityTriplePencilEndpoint_inner :
    let x := infinityTripleScalarX W hΔ
    infinityTripleScalarScale W hΔ 0 * (x 2 - x 0) *
        (infinityTripleNegY W hΔ 3 * x 2 - x 3) =
      (infinityTripleScalarSlope W hΔ 0 - infinityTripleScalarSlope W hΔ 1) *
        infinityTripleForwardCrossDenominator W hΔ 1 0 :=
  infinityTripleScalar_inner_cross W hΔ

/-- The left pencil at the inner output uses a reverse cross denominator, with no unit claim. -/
theorem infinityTriplePencilEndpoint_left :
    let x := infinityTripleScalarX W hΔ;
    -(infinityTripleScalarScale W hΔ 1 * (x 3 - x 1) *
        (infinityTripleNegY W hΔ 4 * x 3 - x 4)) =
      (infinityTripleScalarSlope W hΔ 2 - infinityTripleScalarSlope W hΔ 1) *
        infinityTripleReverseCrossDenominator W hΔ 2 1 := by
  have h := congrArg (fun p => p.eval (infinityTripleScalarX W hΔ 3))
    (infinityTriplePencilPolynomial_left W hΔ)
  rw [infinityTriplePencilPolynomial_eval] at h
  simp only [infinityTriplePointPolynomial, infinityTripleThirdPolynomial,
    eval_sub, eval_mul, eval_C, eval_X, sub_self, mul_zero, zero_mul, zero_sub] at h
  have hl := infinityTripleScalar_line_swap W hΔ 2
  change infinityTripleScalarSlope W hΔ 2 *
    (infinityTripleScalarX W hΔ 3 - infinityTripleScalarX W hΔ 2) =
    infinityTripleScalarZ W hΔ 3 - infinityTripleScalarZ W hΔ 2 at hl
  rw [hl, ← add_sub_assoc, add_sub_cancel_left] at h
  dsimp only [infinityTripleReverseCrossDenominator, infinityTripleNegY]
  rw [show infinityTripleLeftIndex 2 = 3 from rfl,
    show infinityTripleRightIndex 2 = 2 from rfl, h]
  congr 1
  simpa only [infinityCubicDividedZ_one] using infinityCubicDividedZ_swap
    (W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤)))
    (infinityTripleScalarX W hΔ 3) 1 (infinityTripleScalarZ W hΔ 3)
    (infinityTripleScalarZ W hΔ 2 + infinityTripleScalarSlope W hΔ 1 *
      (infinityTripleScalarX W hΔ 3 - infinityTripleScalarX W hΔ 2))

/-- The right pencil at the other inner output uses the forward denominator of the outer law. -/
theorem infinityTriplePencilEndpoint_right :
    let x := infinityTripleScalarX W hΔ
    infinityTripleScalarScale W hΔ 0 * (x 4 - x 1) *
        (infinityTripleNegY W hΔ 3 * x 4 - x 3) =
      (infinityTripleScalarSlope W hΔ 0 - infinityTripleScalarSlope W hΔ 3) *
        infinityTripleForwardCrossDenominator W hΔ 3 0 := by
  have h := congrArg (fun p => p.eval (infinityTripleScalarX W hΔ 4))
    (infinityTriplePencilPolynomial_right W hΔ)
  rw [infinityTriplePencilPolynomial_eval] at h
  simp only [infinityTriplePointPolynomial, infinityTripleThirdPolynomial,
    eval_sub, eval_mul, eval_C, eval_X, sub_self, mul_zero, zero_mul, sub_zero] at h
  have hl := infinityTripleScalar_line W hΔ 3
  change infinityTripleScalarSlope W hΔ 3 *
    (infinityTripleScalarX W hΔ 4 - infinityTripleScalarX W hΔ 0) =
    infinityTripleScalarZ W hΔ 4 - infinityTripleScalarZ W hΔ 0 at hl
  rw [hl, ← add_sub_assoc, add_sub_cancel_left] at h
  exact h

end FLT.Mazur.WeierstrassIntegralChart
