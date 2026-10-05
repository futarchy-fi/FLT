/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeSecantReduction
public import FLT.Mazur.EllipticReductionOpposite

/-!
# Slopes joining opposite nodal branches

At equal positive depth, an integral slope joining the two strict branches
cannot reduce to either nodal tangent. Thus its addition x-coordinate is a
unit. Nonintegral slopes instead give a sum reducing to infinity.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

/-- A line joining the two strict tangent branches has neither tangent slope. -/
theorem node_opposite_slope_not_tangent {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) {a b c d l : R} (ha : IsUnit a) (h1 : IsUnit W.a₁)
    (hb : b ∈ maximalIdeal R) (hd : IsUnit d) (hdt : d + W.a₁ * c ∈ maximalIdeal R)
    (hl : (a - c) * l = b - d) :
    residue R l ≠ 0 ∧ residue R l ≠ -residue R W.a₁ := by
  have he := congrArg (residue R) hl
  have ht := (residue_eq_zero_iff _).mpr hdt
  have hb0 := (residue_eq_zero_iff _).mpr hb
  have hd0 := (residue_ne_zero_iff_isUnit _).mpr hd
  have ha0 := (residue_ne_zero_iff_isUnit _).mpr ha
  have h10 := (residue_ne_zero_iff_isUnit _).mpr h1
  simp only [map_mul, map_sub, hb0, zero_sub] at he
  simp only [map_add, map_mul] at ht
  constructor
  · intro hz
    rw [hz, mul_zero] at he
    exact hd0 (neg_eq_zero.mp he.symm)
  · intro hz
    rw [hz] at he
    apply mul_ne_zero h10 ha0
    linear_combination -he + ht

/-- Cancelling a common nonzero scale in the actual slope identity. -/
theorem node_equal_depth_slope_identity {K : Type*} [Field K] [DecidableEq K]
    (A : ValuationSubring K) (W : WeierstrassCurve A) {π : A} (hπ : π ≠ 0)
    (k : ℕ) (a b c d l : A)
    (h₁ : (W.map (algebraMap A K)).toAffine.Equation
      ((π ^ k * a : A) : K) ((π ^ k * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Equation
      ((π ^ k * c : A) : K) ((π ^ k * d : A) : K))
    (hxy : ¬ (((π ^ k * a : A) : K) = ((π ^ k * c : A) : K) ∧
      ((π ^ k * b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ k * c : A) : K) ((π ^ k * d : A) : K)))
    (hl : (W.map (algebraMap A K)).toAffine.slope
      ((π ^ k * a : A) : K) ((π ^ k * c : A) : K)
      ((π ^ k * b : A) : K) ((π ^ k * d : A) : K) = (l : K)) :
    (a - c) * l = b - d := by
  have he := (slope_cleared_identities _ h₁ h₂ hxy).1
  rw [hl] at he
  have hi : (π ^ k * a - π ^ k * c) * l = π ^ k * b - π ^ k * d := by
    exact_mod_cast he
  apply mul_left_cancel₀ (pow_ne_zero k hπ)
  linear_combination hi

/-- An integral slope away from both nodal tangents gives a unit sum x-coordinate. -/
theorem node_addX_unit_of_not_tangent {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) {x₁ x₂ l : R}
    (h2 : W.a₂ ∈ maximalIdeal R) (hx₁ : x₁ ∈ maximalIdeal R)
    (hx₂ : x₂ ∈ maximalIdeal R)
    (hl : residue R l ≠ 0 ∧ residue R l ≠ -residue R W.a₁) :
    IsUnit (W.toAffine.addX x₁ x₂ l) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  have h20 := (residue_eq_zero_iff _).mpr h2
  have hx10 := (residue_eq_zero_iff _).mpr hx₁
  have hx20 := (residue_eq_zero_iff _).mpr hx₂
  simp only [Affine.addX, map_sub, map_add, map_pow, map_mul, h20, hx10, hx20, sub_zero]
  have he : residue R l ^ 2 + residue R W.a₁ * residue R l =
      residue R l * (residue R l + residue R W.a₁) := by ring
  rw [he]
  exact mul_ne_zero hl.1 (fun h => hl.2 (eq_neg_of_add_eq_zero_left h))

end FLT.Mazur
