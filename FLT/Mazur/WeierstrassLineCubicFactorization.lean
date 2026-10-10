/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityLineCoordinates

/-!
# Splitting the cubic on a line without dividing its leading coefficient

The divided quadratic relation gives a factorization over any commutative ring.
In the infinity chart the final linear factor uses the homogeneous third point;
neither its Y coordinate nor a difference between the inputs is canceled.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve MvPolynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Two roots, with the divided relation retained, split the homogeneous line cubic. -/
theorem lineCubic_factorization {P D : Fin 3 → R} {d : R}
    (hP : W.toProjective.Equation P)
    (hd : cubicPolar W P D + cubicPolar W D P * d +
      eval D W.toProjective.polynomial * d ^ 2 = 0) (s t : R) :
    eval (s • P + t • D) W.toProjective.polynomial =
      t * (t - d * s) * (eval D W.toProjective.polynomial * t +
        (cubicPolar W D P + eval D W.toProjective.polynomial * d) * s) := by
  change eval P W.toProjective.polynomial = 0 at hP
  rw [cubicPolar_expansion, hP]
  linear_combination s ^ 2 * t * hd

/-- The cubic on an infinity secant factors using the homogeneous negated output. -/
theorem infinityLine_factorization {x₁ x₂ z₁ z₂ m : R}
    (hP : W.toProjective.Equation ![x₁, 1, z₁])
    (hl : m * (x₂ - x₁) = z₂ - z₁)
    (hc : m * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁) (X Y : R) :
    eval ![X, Y, m * X + (z₁ - m * x₁) * Y] W.toProjective.polynomial =
      (X - x₁ * Y) * (X - x₂ * Y) *
        (infinityLineLeading W m * X - infinityAdditionXYZ W x₁ x₂ z₁ m 0 * Y) := by
  have he : Y • ![x₁, 1, z₁] + (X - x₁ * Y) • ![1, 0, m] =
      ![X, Y, m * X + (z₁ - m * x₁) * Y] := by
    ext i
    fin_cases i <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> dsimp <;> ring
  have hf := lineCubic_factorization W hP (infinity_line_relation W hl hc)
    Y (X - x₁ * Y)
  rw [he, infinityLineLeading_eq, infinityLineQuadratic_eq] at hf
  rw [hf, infinityAdditionXYZ_x]
  ring

/-- The normalized third point supplies the last factor with its actual output unit. -/
theorem infinityLine_normalized_factorization {x₁ x₂ z₁ z₂ m x z u : R}
    (hP : W.toProjective.Equation ![x₁, 1, z₁])
    (hl : m * (x₂ - x₁) = z₂ - z₁)
    (hc : m * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁)
    (hx : x * u = infinityAdditionXYZ W x₁ x₂ z₁ m 0)
    (hn : (-1 - W.a₁ * x - W.a₃ * z) * u = infinityLineLeading W m)
    (X Y : R) :
    eval ![X, Y, m * X + (z₁ - m * x₁) * Y] W.toProjective.polynomial =
      u * (X - x₁ * Y) * (X - x₂ * Y) *
        ((-1 - W.a₁ * x - W.a₃ * z) * X - x * Y) := by
  rw [infinityLine_factorization W hP hl hc, ← hx, ← hn]
  ring

end FLT.Mazur.WeierstrassIntegralChart
