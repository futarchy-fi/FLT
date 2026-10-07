/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAdditionFormula

/-!
# Vieta's third point under projective normalization of a line

The line direction changes by subtracting a multiple of its base point.
The resulting third-point formula transforms by a unit from the two input
normalizations, without cancelling the line parameter. Thus the formula
also applies when the two inputs coincide.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve MvPolynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The polar coefficient after changing the direction within the same line. -/
theorem cubicPolar_direction_change (P D : Fin 3 → R) (a b u : R) :
    cubicPolar W (a • D + b • P) (u • P) =
      u * (a ^ 2 * cubicPolar W D P + 2 * a * b * cubicPolar W P D +
        3 * b ^ 2 * eval P W.toProjective.polynomial) := by
  simp only [cubicPolar, Projective.eval_polynomial, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Vieta's formula commutes with input normalization even when the line parameter is zero. -/
theorem lineThird_normalize {P D : Fin 3 → R} {d y q u v : R}
    (hP : W.toProjective.Equation P)
    (hd : cubicPolar W P D + cubicPolar W D P * d +
      eval D W.toProjective.polynomial * d ^ 2 = 0)
    (hu : u * y = 1) (hv : v * (y + d * q) = 1) :
    lineThird W (u • P) (y • D + (-q) • P) (d * u * v) =
      (y * (y + d * q)) • lineThird W P D d := by
  let A := eval D W.toProjective.polynomial
  let B := cubicPolar W D P
  let C := cubicPolar W P D
  let E := y • D + (-q) • P
  let K := (y - d * q) * A - q * B
  change eval P W.toProjective.polynomial = 0 at hP
  have he : eval E W.toProjective.polynomial = y * (y + d * q) * K := by
    dsimp only [E, K, A, B]
    rw [cubicPolar_expansion, hP]
    linear_combination y * q ^ 2 * hd
  have ha : eval E W.toProjective.polynomial * u = (y + d * q) * K := by
    linear_combination u * he + (y + d * q) * K * hu
  have hb : eval E W.toProjective.polynomial * (d * u * v) = d * K := by
    linear_combination d * v * ha + d * K * hv
  have hc : cubicPolar W E (u • P) = y * B - 2 * q * C := by
    dsimp only [E]
    rw [cubicPolar_direction_change, hP]
    change u * (y ^ 2 * B + 2 * y * -q * C + 3 * (-q) ^ 2 * 0) = _
    linear_combination (y * B - 2 * q * C) * hu
  change lineThird W (u • P) E (d * u * v) = _
  ext i
  simp only [lineThird, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change eval E W.toProjective.polynomial * (u * P i) -
    (cubicPolar W E (u • P) + eval E W.toProjective.polynomial * (d * u * v)) *
      (y * D i + -q * P i) = y * (y + d * q) * (A * P i - (B + A * d) * D i)
  dsimp only [K] at ha hb
  change C + B * d + A * d ^ 2 = 0 at hd
  linear_combination P i * ha - (y * D i - q * P i) * hc -
    (y * D i - q * P i) * hb + (2 * q * y * D i - 2 * q ^ 2 * P i) * hd

/-- Scaling a direction scales Vieta's representative cubically and rescales its parameter. -/
theorem lineThird_direction_smul (P D : Fin 3 → R) (c d : R) :
    lineThird W P (c • D) d = c ^ 3 • lineThird W P D (c * d) := by
  ext i
  simp only [lineThird, cubicPolar, Projective.eval_polynomial,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end FLT.Mazur.WeierstrassIntegralChart
