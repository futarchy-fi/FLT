/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeOppositeSlope

/-!
# The second slope identity at equal nodal depth

Cancel the common uniformizer power from the second cleared slope identity.
Its residue detects the tangent branch even when the divided x-coordinates
coincide. This includes the doubling chart.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)

/-- The second actual slope identity after cancelling a common coordinate depth. -/
theorem node_equal_depth_second_identity {π : A} (hπ : π ≠ 0)
    (k : ℕ) (a b c d l e₃ e₄ : A) (h3 : W.a₃ = π ^ k * e₃) (h4 : W.a₄ = π ^ k * e₄)
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
    (b + d + W.a₁ * c + e₃) * l =
      π ^ k * (a ^ 2 + a * c + c ^ 2) + W.a₂ * (a + c) + e₄ - W.a₁ * b := by
  have he := (slope_cleared_identities _ h₁ h₂ hxy).2
  rw [hl] at he
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, ValuationSubring.algebraMap_apply] at he
  have hi : (π ^ k * b + π ^ k * d + W.a₁ * (π ^ k * c) + W.a₃) * l =
      (π ^ k * a) ^ 2 + (π ^ k * a) * (π ^ k * c) + (π ^ k * c) ^ 2 +
        W.a₂ * (π ^ k * a + π ^ k * c) + W.a₄ - W.a₁ * (π ^ k * b) := by
    exact_mod_cast he
  rw [h3, h4] at hi
  apply mul_left_cancel₀ (pow_ne_zero k hπ)
  linear_combination hi

/-- Reduction of the second identity; the deep coefficients disappear. -/
theorem node_equal_depth_second_residue {π : A} (hπ : π ≠ 0)
    (hπm : π ∈ maximalIdeal A) (k : ℕ) (hk : 0 < k) (a b c d l e₃ e₄ : A)
    (h2 : W.a₂ ∈ maximalIdeal A) (he₃ : e₃ ∈ maximalIdeal A) (he₄ : e₄ ∈ maximalIdeal A)
    (h3 : W.a₃ = π ^ k * e₃) (h4 : W.a₄ = π ^ k * e₄)
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
    (residue A b + residue A d + residue A W.a₁ * residue A c) * residue A l =
      -(residue A W.a₁ * residue A b) := by
  have he := congrArg (residue A)
    (node_equal_depth_second_identity A W hπ k a b c d l e₃ e₄ h3 h4 h₁ h₂ hxy hl)
  simpa [show residue A π = 0 from (residue_eq_zero_iff _).mpr hπm,
    show residue A W.a₂ = 0 from (residue_eq_zero_iff _).mpr h2,
    show residue A e₃ = 0 from (residue_eq_zero_iff _).mpr he₃,
    show residue A e₄ = 0 from (residue_eq_zero_iff _).mpr he₄, Nat.ne_of_gt hk] using he

end FLT.Mazur
