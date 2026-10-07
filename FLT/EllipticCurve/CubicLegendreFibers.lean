/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendre
/-! # The six Legendre parameters over a fixed j-invariant

An explicit factorization classifies every nonsingular Legendre parameter
with a given j-invariant. The result holds over any field of characteristic
different from two and permits coincidences among the six values.
-/

@[expose] public noncomputable section
namespace WeierstrassCurve.CubicCharts
universe u
variable {K : Type u} [Field K]

/-- Clearing the j denominators gives the product of the six parameter differences. -/
theorem legendre_cross_factorization (l m : K) (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    (m ^ 2 - m + 1) ^ 3 * (l ^ 2 * (l - 1) ^ 2) -
      (l ^ 2 - l + 1) ^ 3 * (m ^ 2 * (m - 1) ^ 2) =
    (l ^ 2 * (l - 1) ^ 2) *
      (m - l) * (m - (1 - l)) * (m - l⁻¹) * (m - (1 - l)⁻¹) *
        (m - l / (l - 1)) * (m - (l - 1) / l) := by
  have h1 : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  have h2 : 1 - l ≠ 0 := sub_ne_zero.mpr hl1.symm
  field_simp
  ring

/-- The cleared equation vanishes precisely at one of the six parameters. -/
theorem legendre_cross_zero_iff (l m : K) (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    (m ^ 2 - m + 1) ^ 3 * (l ^ 2 * (l - 1) ^ 2) -
      (l ^ 2 - l + 1) ^ 3 * (m ^ 2 * (m - 1) ^ 2) = 0 ↔
      m = l ∨ m = 1 - l ∨ m = l⁻¹ ∨ m = (1 - l)⁻¹ ∨
        m = l / (l - 1) ∨ m = (l - 1) / l := by
  rw [legendre_cross_factorization l m hl0 hl1]
  simp only [mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0), sub_eq_zero,
    hl0, hl1, false_or, or_assoc]

/-- Equality of nonsingular Legendre j-invariants is the six-parameter relation. -/
theorem legendre_j_eq_iff_six (l m : K) (h2 : (2 : K) ≠ 0)
    (hl0 : l ≠ 0) (hl1 : l ≠ 1) (hm0 : m ≠ 0) (hm1 : m ≠ 1)
    [(legendreCurve l).IsElliptic] [(legendreCurve m).IsElliptic] :
    (legendreCurve l).j = (legendreCurve m).j ↔
      m = l ∨ m = 1 - l ∨ m = l⁻¹ ∨ m = (1 - l)⁻¹ ∨
        m = l / (l - 1) ∨ m = (l - 1) / l := by
  rw [← legendre_cross_zero_iff l m hl0 hl1,
    legendreCurve_j l h2 hl0 hl1, legendreCurve_j m h2 hm0 hm1]
  have hdl : l ^ 2 * (l - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ (sub_ne_zero.mpr hl1))
  have hdm : m ^ 2 * (m - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hm0) (pow_ne_zero _ (sub_ne_zero.mpr hm1))
  have h256 : (256 : K) ≠ 0 := by
    convert pow_ne_zero 8 h2 using 1
    norm_num
  rw [div_eq_div_iff hdl hdm]
  constructor
  · intro h
    have hz : (256 : K) *
        ((m ^ 2 - m + 1) ^ 3 * (l ^ 2 * (l - 1) ^ 2) -
          (l ^ 2 - l + 1) ^ 3 * (m ^ 2 * (m - 1) ^ 2)) = 0 := by
      linear_combination -h
    exact (mul_eq_zero.mp hz).resolve_left h256
  · intro h
    linear_combination -(256 : K) * h

end WeierstrassCurve.CubicCharts
