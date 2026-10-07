/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Legendre representatives for geometric elliptic curves

The Legendre equation has discriminant 16λ²(λ-1)² and the usual rational
j-invariant. Its degree-six j-polynomial supplies a nonsingular parameter
for every j over an algebraically closed field of characteristic different
from two. Mathlib's classification by j then gives an admissible coordinate
change from every geometric elliptic equation to a Legendre equation.
-/

@[expose] public noncomputable section
open Polynomial
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R]

/-- The Legendre equation y² = x(x-1)(x-λ). -/
def legendreCurve (l : R) : WeierstrassCurve R :=
  ⟨0, -(l + 1), 0, l, 0⟩

/-- The discriminant of the Legendre equation. -/
theorem legendreCurve_discriminant (l : R) :
    (legendreCurve l).Δ = 16 * l ^ 2 * (l - 1) ^ 2 := by
  simp only [legendreCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- The c₄ invariant of the Legendre equation. -/
theorem legendreCurve_c4 (l : R) :
    (legendreCurve l).c₄ = 16 * (l ^ 2 - l + 1) := by
  simp only [legendreCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]
  ring

/-- The Legendre equation is elliptic when 2, λ and λ-1 are units. -/
theorem legendreCurve_elliptic (l : R) (h2 : IsUnit (2 : R))
    (h0 : IsUnit l) (h1 : IsUnit (l - 1)) : (legendreCurve l).IsElliptic := by
  constructor
  rw [legendreCurve_discriminant, show (16 : R) = 2 ^ 4 by norm_num]
  exact ((h2.pow 4).mul (h0.pow 2)).mul (h1.pow 2)

variable {K : Type u} [Field K]

/-- The j-invariant of a nonsingular Legendre equation. -/
theorem legendreCurve_j (l : K) (h2 : (2 : K) ≠ 0) (h0 : l ≠ 0) (h1 : l ≠ 1)
    [(legendreCurve l).IsElliptic] :
    (legendreCurve l).j = 256 * (l ^ 2 - l + 1) ^ 3 / (l ^ 2 * (l - 1) ^ 2) := by
  rw [WeierstrassCurve.j_eq, legendreCurve_c4, legendreCurve_discriminant]
  have h16 : (16 : K) ≠ 0 := by
    convert pow_ne_zero 4 h2 using 1
    norm_num
  field_simp
  ring

/-- The degree-six equation for a Legendre parameter with prescribed j. -/
def legendreJPolynomial (j : R) : R[X] :=
  C 256 * X ^ 6 - C 768 * X ^ 5 + C (1536 - j) * X ^ 4 +
    C (2 * j - 1792) * X ^ 3 + C (1536 - j) * X ^ 2 - C 768 * X + C 256

/-- The Legendre j-polynomial clears the denominator of the j-invariant. -/
theorem legendreJPolynomial_eval (j l : R) :
    (legendreJPolynomial j).eval l =
      256 * (l ^ 2 - l + 1) ^ 3 - j * (l ^ 2 * (l - 1) ^ 2) := by
  simp only [legendreJPolynomial, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  ring

/-- The leading degree-six coefficient is 256. -/
theorem legendreJPolynomial_coeff_six (j : R) :
    (legendreJPolynomial j).coeff 6 = 256 := by
  simp only [legendreJPolynomial, coeff_add, coeff_sub, coeff_C_mul_X_pow]
  norm_num [coeff_C_mul]

/-- The Legendre j-polynomial is nonconstant away from characteristic two. -/
theorem legendreJPolynomial_degree_ne_zero (j : K) (h2 : (2 : K) ≠ 0) :
    (legendreJPolynomial j).degree ≠ 0 := by
  intro hd
  have hz := coeff_eq_zero_of_degree_lt (p := legendreJPolynomial j)
    (show (legendreJPolynomial j).degree < (6 : WithBot ℕ) by rw [hd]; decide)
  rw [legendreJPolynomial_coeff_six] at hz
  have h256 : (256 : K) ≠ 0 := by
    convert pow_ne_zero 8 h2 using 1
    norm_num
  exact h256 hz

/-- Every geometric j-value has a parameter distinct from zero and one. -/
theorem exists_legendre_parameter [IsAlgClosed K] (j : K) (h2 : (2 : K) ≠ 0) :
    ∃ l : K, l ≠ 0 ∧ l ≠ 1 ∧
      256 * (l ^ 2 - l + 1) ^ 3 = j * (l ^ 2 * (l - 1) ^ 2) := by
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_root (legendreJPolynomial j)
    (legendreJPolynomial_degree_ne_zero j h2)
  rw [IsRoot.def, legendreJPolynomial_eval, sub_eq_zero] at hl
  have h256 : (256 : K) ≠ 0 := by
    convert pow_ne_zero 8 h2 using 1
    norm_num
  refine ⟨l, ?_, ?_, hl⟩
  · intro h
    subst l
    norm_num at hl
    exact h256 hl
  · intro h
    subst l
    norm_num at hl
    exact h256 hl

/-- Every geometric elliptic equation away from characteristic two
has a Legendre representative. -/
theorem exists_variableChange_legendre [IsAlgClosed K]
    (E : WeierstrassCurve K) [E.IsElliptic] (h2 : (2 : K) ≠ 0) :
    ∃ (l : K) (C : VariableChange K), l ≠ 0 ∧ l ≠ 1 ∧ C • E = legendreCurve l := by
  obtain ⟨l, h0, h1, hj⟩ := exists_legendre_parameter E.j h2
  have : (legendreCurve l).IsElliptic :=
    legendreCurve_elliptic l (isUnit_iff_ne_zero.mpr h2)
      (isUnit_iff_ne_zero.mpr h0) (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr h1))
  have heq : E.j = (legendreCurve l).j := by
    rw [legendreCurve_j l h2 h0 h1]
    exact (eq_div_iff (mul_ne_zero (pow_ne_zero 2 h0)
      (pow_ne_zero 2 (sub_ne_zero.mpr h1)))).mpr hj.symm
  obtain ⟨C, hC⟩ := E.exists_variableChange_of_j_eq (legendreCurve l) heq
  exact ⟨l, C, h0, h1, hC⟩

end WeierstrassCurve.CubicCharts
