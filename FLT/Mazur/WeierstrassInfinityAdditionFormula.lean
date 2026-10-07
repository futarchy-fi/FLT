/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicPolarization

/-!
# Integral addition formulas near the pair of points at infinity

On the Y = 1 input charts, use the divided difference dz/dx. Its denominator
equals one at the pair (infinity,infinity). Vieta's formula gives the third
intersection without division by dx, so the formula also handles the diagonal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve MvPolynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Vieta's third intersection, homogenized by the leading coefficient of the line cubic. -/
def lineThird (P D : Fin 3 → R) (d : R) : Fin 3 → R :=
  eval D W.toProjective.polynomial • P -
    (cubicPolar W D P + eval D W.toProjective.polynomial * d) • D

/-- The divided quadratic relation suffices for Vieta's point to lie on the cubic. -/
theorem lineThird_equation {P D : Fin 3 → R} {d : R}
    (hP : W.toProjective.Equation P)
    (hd : cubicPolar W P D + cubicPolar W D P * d +
      eval D W.toProjective.polynomial * d ^ 2 = 0) :
    W.toProjective.Equation (lineThird W P D d) := by
  change eval _ _ = 0 at hP ⊢
  have he : lineThird W P D d = eval D W.toProjective.polynomial • P +
      (-(cubicPolar W D P + eval D W.toProjective.polynomial * d)) • D := by
    ext i
    simp only [lineThird, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, cubicPolar_expansion, hP]
  linear_combination
    -eval D W.toProjective.polynomial ^ 2 *
      (cubicPolar W D P + eval D W.toProjective.polynomial * d) * hd

/-- The denominator of dz/dx on the Y = 1 charts, equal to one at (infinity,infinity). -/
def infinitySlopeDenominator (x₂ z₁ z₂ : R) : R :=
  1 + W.a₁ * x₂ + W.a₃ * (z₁ + z₂) - W.a₂ * x₂ ^ 2 -
    W.a₄ * x₂ * (z₁ + z₂) - W.a₆ * (z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2)

/-- The numerator of dz/dx on the Y = 1 charts. -/
def infinitySlopeNumerator (x₁ x₂ z₁ : R) : R :=
  x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * z₁ * (x₁ + x₂) + W.a₄ * z₁ ^ 2 - W.a₁ * z₁

/-- Subtracting the two cubic equations gives the integral divided-difference relation. -/
theorem infinity_equation_difference {x₁ x₂ z₁ z₂ : R}
    (h₁ : W.toProjective.Equation ![x₁, 1, z₁])
    (h₂ : W.toProjective.Equation ![x₂, 1, z₂]) :
    infinitySlopeDenominator W x₂ z₁ z₂ * (z₂ - z₁) =
      infinitySlopeNumerator W x₁ x₂ z₁ * (x₂ - x₁) := by
  rw [Projective.equation_iff] at h₁ h₂
  simp only [Projective.fin3_def_ext] at h₁ h₂
  dsimp only [infinitySlopeDenominator, infinitySlopeNumerator]
  linear_combination h₂ - h₁

/-- Inverting the divided-difference denominator gives the line relation, even on the diagonal. -/
theorem infinity_slope_relation {x₁ x₂ z₁ z₂ m : R}
    (h₁ : W.toProjective.Equation ![x₁, 1, z₁])
    (h₂ : W.toProjective.Equation ![x₂, 1, z₂])
    (hu : IsUnit (infinitySlopeDenominator W x₂ z₁ z₂))
    (hm : m * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁) :
    m * (x₂ - x₁) = z₂ - z₁ := by
  apply hu.mul_left_inj.mp
  linear_combination (x₂ - x₁) * hm - infinity_equation_difference W h₁ h₂

/-- The two slope relations imply the divided quadratic relation in Vieta's formula. -/
theorem infinity_line_relation {x₁ x₂ z₁ z₂ m : R}
    (hl : m * (x₂ - x₁) = z₂ - z₁)
    (hc : m * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁) :
    cubicPolar W ![x₁, 1, z₁] ![1, 0, m] +
      cubicPolar W ![1, 0, m] ![x₁, 1, z₁] * (x₂ - x₁) +
      eval ![1, 0, m] W.toProjective.polynomial * (x₂ - x₁) ^ 2 = 0 := by
  have hz : z₂ = z₁ + m * (x₂ - x₁) := by linear_combination -hl
  rw [hz] at hc
  dsimp only [infinitySlopeDenominator, infinitySlopeNumerator] at hc
  simp only [cubicPolar, Projective.eval_polynomial, Projective.fin3_def_ext]
  linear_combination hc

/-- Homogeneous addition coordinates which are regular at the pair (infinity,infinity). -/
def infinityAdditionXYZ (x₁ x₂ z₁ m : R) : Fin 3 → R :=
  let T := lineThird W ![x₁, 1, z₁] ![1, 0, m] (x₂ - x₁)
  ![T 0, W.toProjective.negY T, T 2]

/-- The infinity-chart addition formula satisfies the integral cubic. -/
theorem infinityAdditionXYZ_equation {x₁ x₂ z₁ z₂ m : R}
    (h₁ : W.toProjective.Equation ![x₁, 1, z₁])
    (hl : m * (x₂ - x₁) = z₂ - z₁)
    (hc : m * infinitySlopeDenominator W x₂ z₁ z₂ =
      infinitySlopeNumerator W x₁ x₂ z₁) :
    W.toProjective.Equation (infinityAdditionXYZ W x₁ x₂ z₁ m) :=
  projective_equation_negate W
    (lineThird_equation W h₁ (infinity_line_relation W hl hc))

/-- The new integral formula specializes along every ring homomorphism. -/
theorem infinityAdditionXYZ_map {S : Type*} [CommRing S] (f : R →+* S)
    (x₁ x₂ z₁ m : R) :
    f ∘ infinityAdditionXYZ W x₁ x₂ z₁ m =
      infinityAdditionXYZ (W.map f) (f x₁) (f x₂) (f z₁) (f m) := by
  ext i
  fin_cases i <;>
    simp [infinityAdditionXYZ, lineThird, cubicPolar, Projective.eval_polynomial,
      Projective.negY, WeierstrassCurve.map, map_ofNat]

/-- At the pair of infinity points the formula has the nonzero normalized value infinity. -/
@[simp] theorem infinityAdditionXYZ_zero : infinityAdditionXYZ W 0 0 0 0 = ![0, 1, 0] := by
  ext i
  fin_cases i <;>
    simp [infinityAdditionXYZ, lineThird, cubicPolar, Projective.eval_polynomial,
      Projective.negY]

end FLT.Mazur.WeierstrassIntegralChart
