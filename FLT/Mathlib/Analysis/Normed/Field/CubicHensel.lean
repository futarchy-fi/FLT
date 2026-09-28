/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Tactic.LinearCombination

/-!
# A cubic fixed-point lemma over complete nonarchimedean fields

The quadratic and cubic coefficients can be bounded separately. This retains
the extra divisibility of the quadratic Taylor term in residue characteristic
three, which the usual derivative-squared version of Hensel's lemma discards.
-/

@[expose] public noncomputable section

namespace IsNonarchimedean

open scoped NNReal

variable {F : Type*} [NormedField F]

/-- The difference of squares is Lipschitz on a nonarchimedean closed ball. -/
theorem norm_sq_sub_sq_le (hna : IsNonarchimedean (norm : F → ℝ))
    {ρ : ℝ} {x y : F} (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    ‖x ^ 2 - y ^ 2‖ ≤ ρ * ‖x - y‖ := by
  rw [show x ^ 2 - y ^ 2 = (x + y) * (x - y) by ring, norm_mul]
  exact mul_le_mul_of_nonneg_right ((hna x y).trans (max_le hx hy)) (norm_nonneg _)

/-- The difference of cubes is Lipschitz on a nonarchimedean closed ball. -/
theorem norm_cube_sub_cube_le (hna : IsNonarchimedean (norm : F → ℝ))
    {ρ : ℝ} {x y : F} (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    ‖x ^ 3 - y ^ 3‖ ≤ ρ ^ 2 * ‖x - y‖ := by
  have hρ : 0 ≤ ρ := (norm_nonneg x).trans hx
  rw [show x ^ 3 - y ^ 3 = (x ^ 2 + x * y + y ^ 2) * (x - y) by ring, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (hna _ _).trans
  apply max_le
  · apply (hna _ _).trans
    apply max_le
    · simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg x) hx 2
    · simpa only [norm_mul, pow_two] using mul_le_mul hx hy (norm_nonneg y) hρ
  · simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg y) hy 2

/-- A cubic perturbation of a constant has a fixed point in a closed ball
when its quadratic and cubic Lipschitz constants are strictly less than one. -/
theorem exists_cubic_fixedPoint [CompleteSpace F]
    (hna : IsNonarchimedean (norm : F → ℝ)) (c u v : F) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hc : ‖c‖ ≤ ρ)
    (hu : ‖u‖ * ρ < 1) (hv : ‖v‖ * ρ ^ 2 < 1) :
    ∃ z : F, ‖z‖ ≤ ρ ∧ z = c + u * z ^ 2 + v * z ^ 3 := by
  let S := {z : F // ‖z‖ ≤ ρ}
  have hclosed : IsClosed {z : F | ‖z‖ ≤ ρ} := isClosed_le continuous_norm continuous_const
  let : CompleteSpace S := hclosed.completeSpace_coe
  let k : ℝ≥0 := ⟨max (‖u‖ * ρ) (‖v‖ * ρ ^ 2),
    le_max_of_le_left (mul_nonneg (norm_nonneg _) hρ)⟩
  have hk : (k : ℝ) < 1 := max_lt hu hv
  have hmap (z : S) : ‖c + u * (z : F) ^ 2 + v * (z : F) ^ 3‖ ≤ ρ := by
    have hz2 := pow_le_pow_left₀ (norm_nonneg (z : F)) z.property 2
    have hz3 := pow_le_pow_left₀ (norm_nonneg (z : F)) z.property 3
    apply (hna _ _).trans
    apply max_le
    · apply (hna _ _).trans
      apply max_le hc
      rw [norm_mul, norm_pow]
      calc
        _ ≤ ‖u‖ * ρ ^ 2 := mul_le_mul_of_nonneg_left hz2 (norm_nonneg _)
        _ = (‖u‖ * ρ) * ρ := by ring
        _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hu.le hρ
        _ = ρ := one_mul _
    · rw [norm_mul, norm_pow]
      calc
        _ ≤ ‖v‖ * ρ ^ 3 := mul_le_mul_of_nonneg_left hz3 (norm_nonneg _)
        _ = (‖v‖ * ρ ^ 2) * ρ := by ring
        _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hv.le hρ
        _ = ρ := one_mul _
  let T : S → S := fun z ↦ ⟨c + u * (z : F) ^ 2 + v * (z : F) ^ 3, hmap z⟩
  have hT : ContractingWith k T := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul fun z w ↦ ?_⟩
    change dist ((T z : S) : F) ((T w : S) : F) ≤ (k : ℝ) * dist (z : F) (w : F)
    rw [dist_eq_norm, dist_eq_norm]
    change ‖(c + u * (z : F) ^ 2 + v * (z : F) ^ 3) -
      (c + u * (w : F) ^ 2 + v * (w : F) ^ 3)‖ ≤ (k : ℝ) * ‖(z : F) - (w : F)‖
    rw [show (c + u * (z : F) ^ 2 + v * (z : F) ^ 3) -
      (c + u * (w : F) ^ 2 + v * (w : F) ^ 3) =
      u * ((z : F) ^ 2 - (w : F) ^ 2) + v * ((z : F) ^ 3 - (w : F) ^ 3) by ring]
    apply (hna _ _).trans
    apply max_le
    · rw [norm_mul]
      calc
        _ ≤ ‖u‖ * (ρ * ‖(z : F) - (w : F)‖) := mul_le_mul_of_nonneg_left
          (hna.norm_sq_sub_sq_le z.property w.property) (norm_nonneg _)
        _ = (‖u‖ * ρ) * ‖(z : F) - (w : F)‖ := (mul_assoc _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    · rw [norm_mul]
      calc
        _ ≤ ‖v‖ * (ρ ^ 2 * ‖(z : F) - (w : F)‖) := mul_le_mul_of_nonneg_left
          (hna.norm_cube_sub_cube_le z.property w.property) (norm_nonneg _)
        _ = (‖v‖ * ρ ^ 2) * ‖(z : F) - (w : F)‖ := (mul_assoc _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  obtain ⟨z, hz, _⟩ := hT.exists_fixedPoint (⟨0, by simpa only [norm_zero] using hρ⟩ : S)
    (edist_ne_top _ _)
  exact ⟨z, z.property, (congrArg Subtype.val hz).symm⟩

/-- A cubic Hensel lemma retaining the norm of three in the quadratic term.
The resulting root lies in the prescribed closed ball around the approximate root. -/
theorem exists_root_cubic_of_norm_bounds [CompleteSpace F]
    (hna : IsNonarchimedean (norm : F → ℝ)) (a b x : F) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hx : ‖x‖ ≤ 1)
    (hf : ‖x ^ 3 + a * x + b‖ ≤ ρ * ‖3 * x ^ 2 + a‖)
    (hq : ‖(3 : F)‖ * ρ < ‖3 * x ^ 2 + a‖)
    (hc : ρ ^ 2 < ‖3 * x ^ 2 + a‖) :
    ∃ y : F, ‖y - x‖ ≤ ρ ∧ y ^ 3 + a * y + b = 0 := by
  let d := 3 * x ^ 2 + a
  have hdpos : 0 < ‖d‖ := (sq_nonneg ρ).trans_lt hc
  have hd0 : d ≠ 0 := norm_pos_iff.mp hdpos
  have hconst : ‖-(x ^ 3 + a * x + b) / d‖ ≤ ρ := by
    rw [norm_div, norm_neg, div_le_iff₀ hdpos]
    exact hf
  have hquad : ‖-(3 * x) / d‖ * ρ < 1 := by
    rw [norm_div, norm_neg, norm_mul]
    calc
      _ ≤ (‖(3 : F)‖ * 1 / ‖d‖) * ρ := by gcongr
      _ = (‖(3 : F)‖ * ρ) / ‖d‖ := by ring
      _ < 1 := (div_lt_one hdpos).mpr hq
  have hcubic : ‖-(1 : F) / d‖ * ρ ^ 2 < 1 := by
    rw [norm_div, norm_neg, norm_one]
    convert (div_lt_one hdpos).mpr hc using 1
    ring
  obtain ⟨z, hz, heq⟩ := hna.exists_cubic_fixedPoint
    (-(x ^ 3 + a * x + b) / d) (-(3 * x) / d) (-(1 : F) / d)
    hρ hconst hquad hcubic
  refine ⟨x + z, by simpa only [add_sub_cancel_left] using hz, ?_⟩
  field_simp [hd0] at heq
  dsimp only [d] at heq
  linear_combination heq

end IsNonarchimedean
