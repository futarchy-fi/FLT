/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineVietaFormula

/-!
# Infinity addition compared with an arbitrary affine line direction

The comparison factor is the cube of the affine intercept. The proof uses
Vieta normalization and the slope relation, including when the line parameter
vanishes. It does not pass through the polynomial addition law's nonzero locus.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve MvPolynomial

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  {x₁ x₂ y₁ y₂ p q d u v m : R}

/-- The change in normalized X is the line parameter times the affine intercept and input units. -/
theorem infinityVieta_parameter (hx : x₂ = x₁ + d * p) (hy : y₂ = y₁ + d * q)
    (hu : u * y₁ = 1) (hv : v * y₂ = 1) :
    (p * y₁ - q * x₁) * (d * u * v) = x₂ * v - x₁ * u := by
  linear_combination -u * v * y₁ * hx + u * v * x₁ * hy + x₂ * v * hu - x₁ * u * hv

/-- The two Vieta representatives compare on the full common chart domain. -/
theorem infinityVieta_third (hP : W.toAffine.Equation x₁ y₁)
    (hd : cubicPolar W ![x₁, y₁, 1] ![p, q, 0] +
      cubicPolar W ![p, q, 0] ![x₁, y₁, 1] * d +
      eval ![p, q, 0] W.toProjective.polynomial * d ^ 2 = 0)
    (hx : x₂ = x₁ + d * p) (hy : y₂ = y₁ + d * q)
    (hu : u * y₁ = 1) (hv : v * y₂ = 1)
    (hm : m * (p * y₁ - q * x₁) = -q) :
    (p * y₁ - q * x₁) ^ 3 •
        lineThird W ![x₁ * u, 1, u] ![1, 0, m] (x₂ * v - x₁ * u) =
      (y₁ * y₂) • lineThird W ![x₁, y₁, 1] ![p, q, 0] d := by
  have hp : u • ![x₁, y₁, 1] = ![x₁ * u, 1, u] := by
    ext i
    fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul] <;> dsimp
    · ring
    · exact hu
    · ring
  have he : y₁ • ![p, q, 0] + (-q) • ![x₁, y₁, 1] =
      (p * y₁ - q * x₁) • ![1, 0, m] := by
    ext i
    fin_cases i <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> dsimp
    · ring
    · ring
    · linear_combination -hm
  have hv' : v * (y₁ + d * q) = 1 := by rw [← hy]; exact hv
  have h := lineThird_normalize W ((Projective.equation_some ..).mpr hP) hd hu hv'
  rw [hp, he, lineThird_direction_smul, infinityVieta_parameter hx hy hu hv, ← hy] at h
  exact h

/-- Elliptic negation preserves the full-domain Vieta comparison factor. -/
theorem infinityVieta_addition (hP : W.toAffine.Equation x₁ y₁)
    (hd : cubicPolar W ![x₁, y₁, 1] ![p, q, 0] +
      cubicPolar W ![p, q, 0] ![x₁, y₁, 1] * d +
      eval ![p, q, 0] W.toProjective.polynomial * d ^ 2 = 0)
    (hx : x₂ = x₁ + d * p) (hy : y₂ = y₁ + d * q)
    (hu : u * y₁ = 1) (hv : v * y₂ = 1)
    (hm : m * (p * y₁ - q * x₁) = -q) :
    let T := lineThird W ![x₁, y₁, 1] ![p, q, 0] d
    (p * y₁ - q * x₁) ^ 3 • infinityAdditionXYZ W (x₁ * u) (x₂ * v) u m =
      (y₁ * y₂) • ![T 0, W.toProjective.negY T, T 2] := by
  have h := infinityVieta_third W hP hd hx hy hu hv hm
  ext i
  fin_cases i
  · exact congrFun h 0
  · have hy := congrArg W.toProjective.negY h
    simp only [Projective.negY_smul] at hy
    exact hy
  · exact congrFun h 2

end FLT.Mazur.WeierstrassIntegralChart
