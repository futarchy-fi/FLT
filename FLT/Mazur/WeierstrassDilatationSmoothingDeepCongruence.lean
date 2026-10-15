/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationInverseArbitraryIdeal
public import FLT.Mazur.WeierstrassDilatationSmoothingCongruence

/-!
# Higher-order control of the actual terminal smoothing constant

If b3 and b4 lie in any deeper ideal J, the constructed smoothing differs
from the original b6 by J squared. The size of b6 is not restricted to first order.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (b3 b4 b6 : R) (r F : R[X])
  (J : Ideal R) (h3J : b3 ∈ J) (h4J : b4 ∈ J)

include h3J h4J in
/-- Removing the retained constant leaves a polynomial in the deeper coefficient ideal. -/
theorem terminalProductCorrection_sub_constant_mem :
    terminalProductCorrection b3 b4 b6 r F - C b6 ∈ J.map C := by
  have h := (J.map C).mul_mem_right F ((J.map C).sub_mem
    (Ideal.mem_map_of_mem C h4J)
    ((J.map C).mul_mem_right (r.comp F) (Ideal.mem_map_of_mem C h3J)))
  simpa only [terminalProductCorrection, add_sub_cancel_left] using h

include h3J h4J in
/-- Differentiation removes b6, retaining the deeper ideal of the linear coefficients. -/
theorem terminalProductCorrection_derivative_mem :
    (terminalProductCorrection b3 b4 b6 r F).derivative ∈ J.map C := by
  have h := NilpotentPolynomialInverse.derivative_mem J
    (terminalProductCorrection b3 b4 b6 r F - C b6)
    (terminalProductCorrection_sub_constant_mem b3 b4 b6 r F J h3J h4J)
  simpa only [derivative_sub, derivative_C, sub_zero] using h

variable (W : WeierstrassCurve R) (I : Ideal R) (hI : IsNilpotent I)
  (hrI : r ∈ I.map C) (ha : IsUnit W.a₁) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "F₀" => terminalInversePolynomial W r I hI hrI ha
local notation "H" => terminalProductCorrection b3 b4 b6 r F₀
local notation "hH" => terminalProductCorrection_mem b3 b4 b6 r F₀ I h4 h6 hrI
local notation "z" => DifferenceNode.criticalDifference H b3 I hI hH
local notation "a" => DifferenceNode.criticalSlope H b3 I hI hH

include h3J h4J in
/-- The constructed critical slope retains any deeper ideal containing b3 and b4. -/
theorem terminalCriticalSlope_mem_ideal : a ∈ J := by
  simpa only [DifferenceNode.criticalSlope, eval₂_id, Ideal.map_id] using
    NilpotentPolynomialInverse.eval₂_mem J (RingHom.id R) (H).derivative
      (terminalProductCorrection_derivative_mem b3 b4 b6 r F₀ J h3J h4J) z

include h3J h4J in
/-- The exact smoothing correction lies in the square of the deeper linear-coefficient ideal. -/
theorem terminalSmoothing_sub_mem_ideal_sq :
    terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6 - b6 ∈ J ^ 2 := by
  have haJ := terminalCriticalSlope_mem_ideal b3 b4 b6 r J h3J h4J W I hI hrI ha h4 h6
  have hz : z ∈ J := by
    have he : z = -b3 - a - a := by
      linear_combination DifferenceNode.criticalDifference_equation H b3 I hI hH
    rw [he]
    exact J.sub_mem (J.sub_mem (J.neg_mem h3J) haJ) haJ
  have ht := terminalInversePolynomial_eval_mem_ideal W r I hI hrI ha J z hz
  have hm : (b4 - b3 * r.eval ((F₀).eval z)) * (F₀).eval z ∈ J ^ 2 := by
    simpa only [pow_two] using
      Ideal.mul_mem_mul (J.sub_mem h4J (J.mul_mem_right _ h3J)) ht
  have ha2 : a ^ 2 ∈ J ^ 2 := Ideal.pow_mem_pow haJ 2
  convert (J ^ 2).add_mem hm ha2 using 1
  rw [terminalSmoothing_formula]
  ring

end FLT.Mazur.WeierstrassDilatation
