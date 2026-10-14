/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeSameBranchSlope
public import FLT.Mazur.EllipticNodeMiddleAddition

/-!
# Middle-depth character algebra in exceptional slope charts

The second slope identity computes the smooth character in the integral chart.
If the sum is vertical or the slope is nonintegral, its divided denominator
vanishes in the residue field. This gives the same character law at infinity.
-/

@[expose] public section
namespace FLT.Mazur
open IsLocalRing WeierstrassCurve

/-- The second slope identity computes the middle-depth smooth character. -/
theorem node_middle_slope_character {R : Type*} [CommRing R] [IsLocalRing R]
    (W : WeierstrassCurve R) {b c d l : R} (h1 : IsUnit W.a₁)
    (hb : IsUnit b) (hd : IsUnit (d + W.a₁ * c))
    (hl : (residue R b + residue R d + residue R W.a₁ * residue R c) * residue R l =
      -(residue R W.a₁ * residue R b)) :
    residue R b * ((residue R l + residue R W.a₁) / residue R l) =
      -residue R (d + W.a₁ * c) := by
  have hn := (node_middle_slope_not_tangent W h1 hb hd hl).1
  rw [map_add, map_mul]
  apply mul_right_cancel₀ hn
  field_simp
  linear_combination hl

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)

/-- Vertical and nonintegral sums force the divided second denominator to vanish. -/
theorem node_exceptional_second_residue {π : A} (hπ : π ≠ 0)
    (k : ℕ) (a b c d e₃ e₄ : A) (he₃ : e₃ ∈ maximalIdeal A)
    (h3 : W.a₃ = π ^ k * e₃) (h4 : W.a₄ = π ^ k * e₄)
    (h₁ : (W.map (algebraMap A K)).toAffine.Equation
      ((π ^ k * a : A) : K) ((π ^ k * b : A) : K))
    (h₂ : (W.map (algebraMap A K)).toAffine.Equation
      ((π ^ k * c : A) : K) ((π ^ k * d : A) : K))
    (hex : ((π ^ k * b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
        ((π ^ k * c : A) : K) ((π ^ k * d : A) : K) ∨
      (W.map (algebraMap A K)).toAffine.slope
        ((π ^ k * a : A) : K) ((π ^ k * c : A) : K)
        ((π ^ k * b : A) : K) ((π ^ k * d : A) : K) ∉ A) :
    residue A b = -residue A (d + W.a₁ * c) := by
  by_contra hne
  have hu : IsUnit (b + d + W.a₁ * c + e₃) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    rw [map_add, (residue_eq_zero_iff _).mpr he₃, add_zero,
      map_add, map_add, map_mul]
    rw [map_add, map_mul] at hne
    intro hz
    apply hne
    linear_combination hz
  obtain ⟨l, hl, hy⟩ := exists_node_second_slope A W hπ k a b c d e₃ e₄ h3 h4 hu h₁ h₂
  rcases hex with h | h
  · exact hy h
  · exact h (hl ▸ l.property)

end FLT.Mazur
