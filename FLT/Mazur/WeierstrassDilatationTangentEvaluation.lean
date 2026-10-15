/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTangentCorrection

/-!
# Recovering the full terminal equation from the corrected tangent product

The polynomial inverse and the unchanged product relation construct actual
solutions of the original divided cubic, including at the horizontal origin.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (r : R[X]) (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
  (hr : r ^ 2 + C W.a₁ * r = C W.a₂ + C s * X)
  {S : Type*} [CommRing S] [Algebra R S] (p q : S)
local notation "f" => algebraMap R S
local notation "F" => terminalInversePolynomial W r I hI hrI ha
local notation "T" => Polynomial.eval₂ (algebraMap R S)
  (q - p - algebraMap R S b3) (terminalInversePolynomial W r I hI hrI ha)
local notation "V" => r.eval₂ f T

variable (hpq : p * q = (terminalProductCorrection b3 b4 b6 r
  (terminalInversePolynomial W r I hI hrI ha)).eval₂ (algebraMap R S)
    (q - p - algebraMap R S b3))

include hr hpq in
/-- The recovered coordinates satisfy the original full terminal cubic. -/
theorem terminalTangentEvaluation_equation :
    (p + T * V) ^ 2 + (f W.a₁ * T + f b3) * (p + T * V) =
      f s * T ^ 3 + f W.a₂ * T ^ 2 + f b4 * T + f b6 := by
  have hx := terminalInversePolynomial_eval_equation W r I hI hrI ha
    (q - p - f b3)
  have hr' := congrArg (Polynomial.eval₂ f T) hr
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X] at hr'
  rw [terminalProductCorrection_eval] at hpq
  linear_combination hpq + T ^ 2 * hr' + p * hx

/-- The actual evaluation of the original terminal coordinate algebra. -/
def terminalTangentEvaluation : Coordinate W s b3 b4 b6 →ₐ[R] S :=
  evaluation W s b3 b4 b6 T (p + T * V)
    (terminalTangentEvaluation_equation W s b3 b4 b6 r I hI hrI ha hr p q hpq)

/-- The recovered horizontal coordinate is the polynomial in the difference. -/
@[simp] theorem terminalTangentEvaluation_x :
    terminalTangentEvaluation W s b3 b4 b6 r I hI hrI ha hr p q hpq
      (x W s b3 b4 b6) = T := evaluation_x ..

/-- The recovered ordinate retains the small tangent shift. -/
@[simp] theorem terminalTangentEvaluation_y :
    terminalTangentEvaluation W s b3 b4 b6 r I hI hrI ha hr p q hpq
      (y W s b3 b4 b6) = p + T * V := evaluation_y ..

/-- Evaluation of every horizontal polynomial uses the recovered x. -/
theorem terminalTangentEvaluation_polynomial (k : R[X]) :
    terminalTangentEvaluation W s b3 b4 b6 r I hI hrI ha hr p q hpq
      (algebraMap R[X] (Coordinate W s b3 b4 b6) k) = k.eval₂ f T := by
  have he : k.eval₂ (algebraMap R (Coordinate W s b3 b4 b6)) (x W s b3 b4 b6) =
      algebraMap R[X] (Coordinate W s b3 b4 b6) k :=
    Polynomial.eval₂_algebraMap_X k (Algebra.algHom R R[X] _)
  rw [← he, Polynomial.algHom_eval₂_algebraMap, terminalTangentEvaluation_x]

/-- The first tangent factor is recovered on every point of the corrected quotient. -/
theorem terminalTangentEvaluation_small :
    terminalTangentEvaluation W s b3 b4 b6 r I hI hrI ha hr p q hpq
      (terminalSmallTangent W s b3 b4 b6 r) = p := by
  simp only [terminalSmallTangent, map_sub, map_mul, terminalTangentEvaluation_y,
    terminalTangentEvaluation_x, terminalTangentEvaluation_polynomial, add_sub_cancel_right]

/-- The opposite tangent factor is recovered without localizing either tangent. -/
theorem terminalTangentEvaluation_opposite :
    terminalTangentEvaluation W s b3 b4 b6 r I hI hrI ha hr p q hpq
      (terminalOppositeTangent W s b3 b4 b6 r) = q := by
  simp only [terminalOppositeTangent, map_add, map_mul, AlgHom.commutes,
    terminalTangentEvaluation_y, terminalTangentEvaluation_x, terminalTangentEvaluation_polynomial]
  linear_combination terminalInversePolynomial_eval_equation W r I hI hrI ha
    (q - p - f b3)

end FLT.Mazur.WeierstrassDilatation
