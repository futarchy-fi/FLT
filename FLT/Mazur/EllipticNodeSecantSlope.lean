/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeBranchInverse
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Secant slopes between different nodal depths

When the first point has smaller depth and unit divided x-coordinate,
cancel its common power from the secant denominator. The remaining denominator
is a unit, so the actual field slope is integral. Its residue is the tangent
slope of the shallower point.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

section LocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The divided secant denominator at distinct depths is a unit. -/
theorem node_secant_denominator_unit {π a : R} (hπ : π ∈ maximalIdeal R)
    (ha : IsUnit a) (j : ℕ) (hj : 0 < j) (c : R) : IsUnit (a - π ^ j * c) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  simpa [show residue R π = 0 from (residue_eq_zero_iff _).mpr hπ,
    Nat.ne_of_gt hj] using (residue_ne_zero_iff_isUnit _).mpr ha

/-- Cancelling the common depth gives an integral secant slope with its residue equation. -/
theorem exists_node_secant_slope {π a : R} (hπ : π ∈ maximalIdeal R) (ha : IsUnit a)
    (j : ℕ) (hj : 0 < j) (b c d : R) :
    ∃ l : R, l * (a - π ^ j * c) = b - π ^ j * d ∧
      residue R l * residue R a = residue R b := by
  obtain ⟨u, hu⟩ := node_secant_denominator_unit hπ ha j hj c
  let l : R := (b - π ^ j * d) * ↑u⁻¹
  have he : l * (a - π ^ j * c) = b - π ^ j * d := by
    rw [← hu]
    simp [l, mul_assoc]
  refine ⟨l, he, ?_⟩
  have hr := congrArg (residue R) he
  simpa [show residue R π = 0 from (residue_eq_zero_iff _).mpr hπ,
    Nat.ne_of_gt hj] using hr

/-- The residue slope lies on one of the two distinct nodal tangents. -/
theorem node_secant_residue_tangent (W : WeierstrassCurve R) {a b l : R}
    (ha : IsUnit a) (hl : residue R l * residue R a = residue R b)
    (hb : residue R b * (residue R b + residue R W.a₁ * residue R a) = 0) :
    residue R l = 0 ∨ residue R l = -residue R W.a₁ := by
  have ha0 := (residue_ne_zero_iff_isUnit _).mpr ha
  have he : (residue R l * (residue R l + residue R W.a₁)) * residue R a ^ 2 = 0 := by
    rw [← hl] at hb
    linear_combination hb
  have hz := (mul_eq_zero.mp he).resolve_right (pow_ne_zero 2 ha0)
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

end LocalRing

/-- The cancelled integral slope is exactly the actual Weierstrass secant slope. -/
theorem node_secant_slope_eq {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
    (W : WeierstrassCurve A) {π a : A} (hπ0 : π ≠ 0) (hπ : π ∈ maximalIdeal A)
    (ha : IsUnit a) (k j : ℕ) (hj : 0 < j) (b c d l : A)
    (hl : l * (a - π ^ j * c) = b - π ^ j * d) :
    (W.map (algebraMap A K)).toAffine.slope
      ((π ^ k * a : A) : K) ((π ^ (k + j) * c : A) : K)
      ((π ^ k * b : A) : K) ((π ^ (k + j) * d : A) : K) = (l : K) := by
  have hden : π ^ k * a - π ^ (k + j) * c ≠ 0 := by
    have he : π ^ k * a - π ^ (k + j) * c = π ^ k * (a - π ^ j * c) := by
      rw [pow_add]
      ring
    rw [he]
    exact mul_ne_zero (pow_ne_zero k hπ0) (node_secant_denominator_unit hπ ha j hj c).ne_zero
  have hdenK : ((π ^ k * a : A) : K) - ((π ^ (k + j) * c : A) : K) ≠ 0 := by
    exact_mod_cast hden
  rw [Affine.slope_of_X_ne (sub_ne_zero.mp hdenK), div_eq_iff hdenK]
  have he : π ^ k * b - π ^ (k + j) * d = l * (π ^ k * a - π ^ (k + j) * c) := by
    rw [pow_add]
    linear_combination -π ^ k * hl
  exact_mod_cast he

end FLT.Mazur
