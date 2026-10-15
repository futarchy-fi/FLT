/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationInversePolynomial
public import FLT.Mazur.NilpotentPolynomialEvaluation

/-!
# The retained terminal correction as a polynomial in the tangent difference

The actual constant b6 and the residual linear term are retained. No division
by a tangent coordinate or by the horizontal coordinate occurs.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (b3 b4 b6 : R) (r F : R[X])

/-- The complete product correction in the new difference coordinate. -/
def terminalProductCorrection : R[X] :=
  C b6 + (C b4 - C b3 * r.comp F) * F

/-- Evaluation preserves the original constant and linear correction exactly. -/
theorem terminalProductCorrection_eval {S : Type*} [CommRing S] (f : R →+* S) (d : S) :
    (terminalProductCorrection b3 b4 b6 r F).eval₂ f d =
      f b6 + (f b4 - f b3 * r.eval₂ f (F.eval₂ f d)) * F.eval₂ f d := by
  simp only [terminalProductCorrection, eval₂_add, eval₂_mul, eval₂_sub, eval₂_C,
    eval₂_comp]

variable (I : Ideal R) (h4 : b4 ∈ I) (h6 : b6 ∈ I) (hrI : r ∈ I.map C)

include h4 h6 hrI in
/-- Every coefficient of the remaining correction lies in the arithmetic ideal. -/
theorem terminalProductCorrection_mem : terminalProductCorrection b3 b4 b6 r F ∈ I.map C :=
  (I.map C).add_mem (Ideal.mem_map_of_mem C h6) ((I.map C).mul_mem_right _
    ((I.map C).sub_mem (Ideal.mem_map_of_mem C h4) ((I.map C).mul_mem_left _
      (by
        simpa only [comp] using
          NilpotentPolynomialInverse.eval₂_mem I C r hrI F))))

variable (W : WeierstrassCurve R) (s : R)
  (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (hr : r ^ 2 + C W.a₁ * r = C W.a₂ + C s * X)

local notation "A" => Coordinate W s b3 b4 b6
local notation "P" => terminalSmallTangent W s b3 b4 b6 r
local notation "Q" => terminalOppositeTangent W s b3 b4 b6 r

include hr in
/-- The original tangent coordinates satisfy the entire new polynomial quotient equation. -/
theorem terminalTangents_correction : P * Q =
    (terminalProductCorrection b3 b4 b6 r
      (terminalInversePolynomial W r I hI hrI ha)).eval₂ (algebraMap R A)
        (Q - P - algebraMap R A b3) := by
  rw [terminalProductCorrection_eval, terminalInversePolynomial_original]
  have he : r.eval₂ (algebraMap R A) (x W s b3 b4 b6) = algebraMap R[X] A r :=
    Polynomial.eval₂_algebraMap_X r (Algebra.algHom R R[X] A)
  rw [he]
  exact terminalTangents_product W s b3 b4 b6 r hr

end FLT.Mazur.WeierstrassDilatation
