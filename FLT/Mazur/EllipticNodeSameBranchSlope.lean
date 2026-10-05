/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeEqualDepthSlope

/-!
# Integral slopes on one strict branch

The second secant denominator, divided by the common depth, is a unit on the
first strict branch. This also covers the tangent chart. The resulting
integral slope has residue zero.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

/-- The divided second denominator is a unit on the first strict branch. -/
theorem node_same_branch_denominator_unit {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) {b c d e : R} (h1 : IsUnit W.a₁) (hc : IsUnit c)
    (hb : b ∈ maximalIdeal R) (hd : d ∈ maximalIdeal R) (he : e ∈ maximalIdeal R) :
    IsUnit (b + d + W.a₁ * c + e) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  simpa [show residue R b = 0 from (residue_eq_zero_iff _).mpr hb,
    show residue R d = 0 from (residue_eq_zero_iff _).mpr hd,
    show residue R e = 0 from (residue_eq_zero_iff _).mpr he] using
    mul_ne_zero ((residue_ne_zero_iff_isUnit _).mpr h1) ((residue_ne_zero_iff_isUnit _).mpr hc)

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)

/-- A unit divided second denominator makes the actual slope integral, including doubling. -/
theorem exists_node_second_slope {π : A} (hπ : π ≠ 0) (k : ℕ) (a b c d e₃ e₄ : A)
    (h3 : W.a₃ = π ^ k * e₃) (h4 : W.a₄ = π ^ k * e₄)
    (hu : IsUnit (b + d + W.a₁ * c + e₃))
    (h₁ : (W.map (algebraMap A K)).toAffine.Equation
      ((π ^ k * a : A) : K) ((π ^ k * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Equation
      ((π ^ k * c : A) : K) ((π ^ k * d : A) : K)) :
    ∃ l : A,
      (W.map (algebraMap A K)).toAffine.slope
        ((π ^ k * a : A) : K) ((π ^ k * c : A) : K)
        ((π ^ k * b : A) : K) ((π ^ k * d : A) : K) = (l : K) ∧
      ((π ^ k * b : A) : K) ≠ (W.map (algebraMap A K)).toAffine.negY
        ((π ^ k * c : A) : K) ((π ^ k * d : A) : K) := by
  let t := b + d + W.a₁ * c + e₃
  let r := π ^ k * (a ^ 2 + a * c + c ^ 2) + W.a₂ * (a + c) + e₄ - W.a₁ * b
  obtain ⟨u, hu⟩ := hu
  let l : A := r * ↑u⁻¹
  have hl : l * t = r := by simp [l, t, ← hu, mul_assoc]
  have ht : π ^ k * b + π ^ k * d + W.a₁ * (π ^ k * c) + W.a₃ = π ^ k * t := by
    rw [h3]
    dsimp [t]
    ring
  have ht0 : π ^ k * b + π ^ k * d + W.a₁ * (π ^ k * c) + W.a₃ ≠ 0 := by
    rw [ht]
    exact mul_ne_zero (pow_ne_zero k hπ) (by simpa only [t, ← hu] using u.isUnit.ne_zero)
  have htK : ((π ^ k * b : A) : K) + ((π ^ k * d : A) : K) +
      (W.a₁ : K) * ((π ^ k * c : A) : K) + (W.a₃ : K) ≠ 0 := by exact_mod_cast ht0
  have hy : ((π ^ k * b : A) : K) ≠ (W.map (algebraMap A K)).toAffine.negY
      ((π ^ k * c : A) : K) ((π ^ k * d : A) : K) := by
    intro he
    apply htK
    simp only [Affine.negY, map_a₁, map_a₃, ValuationSubring.algebraMap_apply] at he
    linear_combination he
  refine ⟨l, ?_, hy⟩
  rw [Affine.slope_eq_of_Y_ne _ h₁ h₂ hy]
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, ValuationSubring.algebraMap_apply]
  rw [div_eq_iff htK]
  have he : (π ^ k * a) ^ 2 + (π ^ k * a) * (π ^ k * c) + (π ^ k * c) ^ 2 +
      W.a₂ * (π ^ k * a + π ^ k * c) + W.a₄ - W.a₁ * (π ^ k * b) =
      l * (π ^ k * b + π ^ k * d + W.a₁ * (π ^ k * c) + W.a₃) := by
    rw [h3, h4]
    dsimp [t, r] at hl
    linear_combination -π ^ k * hl
  exact_mod_cast he

end FLT.Mazur
