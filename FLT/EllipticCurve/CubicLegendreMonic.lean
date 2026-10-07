/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendre
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.ComputeDegree

/-! # The monic Legendre relation

Dividing the degree-six j-relation by 256 gives a monic polynomial.
Every root and its difference from one are units. These identities
hold over commutative rings and supply the integral presentation of
the Legendre map to the j-line.
-/

@[expose] public noncomputable section
open Polynomial
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- The monic degree-six relation with normalized parameter k = j/256. -/
def legendreMonicPolynomial (k : R) : R[X] :=
  X ^ 6 - C 3 * X ^ 5 + C (6 - k) * X ^ 4 +
    C (2 * k - 7) * X ^ 3 + C (6 - k) * X ^ 2 - C 3 * X + 1

/-- The normalized Legendre polynomial is monic. -/
theorem legendreMonicPolynomial_monic (k : R) : (legendreMonicPolynomial k).Monic := by
  apply monic_of_degree_le 6
  · unfold legendreMonicPolynomial
    compute_degree
    norm_num
  · simp only [legendreMonicPolynomial, coeff_add, coeff_sub, coeff_C_mul_X_pow]
    norm_num [coeff_C_mul, coeff_one]

/-- Evaluation gives the normalized j-relation. -/
theorem legendreMonicPolynomial_eval (k x : R) :
    (legendreMonicPolynomial k).eval x =
      (x ^ 2 - x + 1) ^ 3 - k * (x ^ 2 * (x - 1) ^ 2) := by
  simp only [legendreMonicPolynomial, eval_add, eval_sub, eval_mul, eval_pow,
    eval_C, eval_X, eval_one]
  ring

/-- The relation is invariant under exchanging zero and one. -/
theorem legendreMonicPolynomial_one_sub (k x : R) :
    (legendreMonicPolynomial k).eval (1 - x) = (legendreMonicPolynomial k).eval x := by
  rw [legendreMonicPolynomial_eval, legendreMonicPolynomial_eval]
  ring

/-- Every root of the monic relation is a unit. -/
theorem legendreMonicPolynomial_root_unit (k x : R)
    (h : (legendreMonicPolynomial k).eval x = 0) : IsUnit x := by
  apply IsUnit.of_mul_eq_one
    (-x ^ 5 + 3 * x ^ 4 - (6 - k) * x ^ 3 - (2 * k - 7) * x ^ 2 - (6 - k) * x + 3)
  rw [legendreMonicPolynomial_eval] at h
  linear_combination -h

/-- Every root differs from one by a unit. -/
theorem legendreMonicPolynomial_root_sub_one_unit (k x : R)
    (h : (legendreMonicPolynomial k).eval x = 0) : IsUnit (x - 1) := by
  have hu := legendreMonicPolynomial_root_unit k (1 - x)
    ((legendreMonicPolynomial_one_sub k x).trans h)
  simpa only [neg_sub] using hu.neg

/-- The j-invariant multiplied by the discriminant is c₄ cubed. -/
theorem elliptic_j_mul_discriminant (E : WeierstrassCurve R) [E.IsElliptic] :
    E.j * E.Δ = E.c₄ ^ 3 := by
  rw [WeierstrassCurve.j, ← E.coe_Δ']
  calc
    (↑E.Δ'⁻¹ * E.c₄ ^ 3) * ↑E.Δ' = (↑E.Δ'⁻¹ * ↑E.Δ') * E.c₄ ^ 3 := by ring
    _ = E.c₄ ^ 3 := by rw [Units.inv_mul, one_mul]

/-- The denominator-free Legendre j-equation over a ring. -/
theorem legendreCurve_j_equation (x : R) [(legendreCurve x).IsElliptic]
    (h2 : IsUnit (2 : R)) :
    256 * (x ^ 2 - x + 1) ^ 3 =
      (legendreCurve x).j * (x ^ 2 * (x - 1) ^ 2) := by
  have hj := elliptic_j_mul_discriminant (legendreCurve x)
  rw [legendreCurve_discriminant, legendreCurve_c4] at hj
  apply (h2.pow 4).mul_left_cancel
  linear_combination -hj

/-- The monic relation commutes with a change of coefficient ring. -/
theorem legendreMonicPolynomial_map {S : Type*} [CommRing S]
    (f : R →+* S) (k : R) :
    (legendreMonicPolynomial k).map f = legendreMonicPolynomial (f k) := by
  simp [legendreMonicPolynomial, map_ofNat]


/-- A Legendre parameter solves the monic equation for its normalized j. -/
theorem legendreMonicPolynomial_j_root (x k : R) [(legendreCurve x).IsElliptic]
    (h2 : IsUnit (2 : R)) (hk : 256 * k = (legendreCurve x).j) :
    (legendreMonicPolynomial k).eval x = 0 := by
  rw [legendreMonicPolynomial_eval]
  apply (h2.pow 8).mul_left_cancel
  linear_combination legendreCurve_j_equation x h2 - (x ^ 2 * (x - 1) ^ 2) * hk

/-- Evaluation after a coefficient map gives the same normalized relation. -/
theorem legendreMonicPolynomial_eval₂ {S : Type*} [CommRing S]
    (f : R →+* S) (k : R) (x : S) :
    (legendreMonicPolynomial k).eval₂ f x =
      (x ^ 2 - x + 1) ^ 3 - f k * (x ^ 2 * (x - 1) ^ 2) := by
  rw [← eval_map, legendreMonicPolynomial_map, legendreMonicPolynomial_eval]

end WeierstrassCurve.CubicCharts
