/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Tactic.LinearCombination

/-!
# Cubic correction in a complete nonarchimedean algebra

A cubic fixed-point argument works in a commutative Banach algebra, without
requiring division by the approximate root. This form applies to convolution
algebras, where scalar division by three has norm three.
-/

@[expose] public noncomputable section

namespace IsNonarchimedean

open scoped NNReal

variable {B : Type*} [NormedCommRing B]

/-- The square difference bound for a submultiplicative nonarchimedean norm. -/
theorem norm_sq_sub_sq_le_algebra (hna : IsNonarchimedean (norm : B → ℝ))
    {ρ : ℝ} {x y : B} (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    ‖x ^ 2 - y ^ 2‖ ≤ ρ * ‖x - y‖ := by
  rw [show x ^ 2 - y ^ 2 = (x + y) * (x - y) by ring]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    ((hna x y).trans (max_le hx hy)) (norm_nonneg _))

/-- The cube difference bound for a submultiplicative nonarchimedean norm. -/
theorem norm_cube_sub_cube_le_algebra (hna : IsNonarchimedean (norm : B → ℝ))
    {ρ : ℝ} {x y : B} (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    ‖x ^ 3 - y ^ 3‖ ≤ ρ ^ 2 * ‖x - y‖ := by
  have hρ : 0 ≤ ρ := (norm_nonneg x).trans hx
  rw [show x ^ 3 - y ^ 3 = (x ^ 2 + x * y + y ^ 2) * (x - y) by ring]
  apply (norm_mul_le _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (hna _ _).trans
  apply max_le
  · apply (hna _ _).trans
    apply max_le
    · exact (norm_pow_le' _ (by norm_num)).trans (pow_le_pow_left₀ (norm_nonneg x) hx 2)
    · apply (norm_mul_le _ _).trans
      simpa only [pow_two] using (mul_le_mul hx hy (norm_nonneg y) hρ)
  · exact (norm_pow_le' _ (by norm_num)).trans (pow_le_pow_left₀ (norm_nonneg y) hy 2)

/-- A cubic polynomial map contracts a closed ball when each of its three
nonconstant terms has Lipschitz constant less than one there. -/
theorem exists_cubic_fixedPoint_algebra [CompleteSpace B]
    (hna : IsNonarchimedean (norm : B → ℝ)) (c a b d : B) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hc : ‖c‖ ≤ ρ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ * ρ < 1) (hd : ‖d‖ * ρ ^ 2 < 1) :
    ∃ z : B, ‖z‖ ≤ ρ ∧ z = c + a * z + b * z ^ 2 + d * z ^ 3 := by
  let S := {z : B // ‖z‖ ≤ ρ}
  have hclosed : IsClosed {z : B | ‖z‖ ≤ ρ} := isClosed_le continuous_norm continuous_const
  let completeBall : CompleteSpace S := hclosed.completeSpace_coe
  let k : ℝ≥0 := ⟨max (max ‖a‖ (‖b‖ * ρ)) (‖d‖ * ρ ^ 2),
    le_max_of_le_left (le_max_of_le_left (norm_nonneg _))⟩
  have hk : (k : ℝ) < 1 := max_lt (max_lt ha hb) hd
  have hdiff (z w : S) :
      ‖(c + a * (z : B) + b * (z : B) ^ 2 + d * (z : B) ^ 3) -
        (c + a * (w : B) + b * (w : B) ^ 2 + d * (w : B) ^ 3)‖ ≤
      (k : ℝ) * ‖(z : B) - (w : B)‖ := by
    rw [show (c + a * (z : B) + b * (z : B) ^ 2 + d * (z : B) ^ 3) -
      (c + a * (w : B) + b * (w : B) ^ 2 + d * (w : B) ^ 3) =
      a * ((z : B) - w) + b * ((z : B) ^ 2 - (w : B) ^ 2) +
        d * ((z : B) ^ 3 - (w : B) ^ 3) by ring]
    apply (hna _ _).trans
    apply max_le
    · apply (hna _ _).trans
      apply max_le
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (le_max_of_le_left (le_max_left _ _)) (norm_nonneg _))
      · calc
          _ ≤ ‖b‖ * (ρ * ‖(z : B) - w‖) := (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left
              (hna.norm_sq_sub_sq_le_algebra z.property w.property) (norm_nonneg _))
          _ = (‖b‖ * ρ) * ‖(z : B) - w‖ := (mul_assoc _ _ _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (le_max_of_le_left (le_max_right _ _)) (norm_nonneg _)
    · calc
        _ ≤ ‖d‖ * (ρ ^ 2 * ‖(z : B) - w‖) := (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_left
            (hna.norm_cube_sub_cube_le_algebra z.property w.property) (norm_nonneg _))
        _ = (‖d‖ * ρ ^ 2) * ‖(z : B) - w‖ := (mul_assoc _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  have hmap (z : S) : ‖c + a * (z : B) + b * (z : B) ^ 2 + d * (z : B) ^ 3‖ ≤ ρ := by
    have h := hdiff z ⟨0, by simpa using hρ⟩
    simp only [sub_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0),
      mul_zero, add_zero] at h
    have hh := hna ((c + a * (z : B) + b * (z : B) ^ 2 + d * (z : B) ^ 3) - c) c
    rw [sub_add_cancel] at hh
    exact hh.trans (max_le (h.trans ((mul_le_mul_of_nonneg_left z.property k.coe_nonneg).trans
      (by simpa using mul_le_mul_of_nonneg_right hk.le hρ))) hc)
  let T : S → S := fun z ↦ ⟨c + a * (z : B) + b * (z : B) ^ 2 + d * (z : B) ^ 3, hmap z⟩
  have hT : ContractingWith k T := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul fun z w ↦ ?_⟩
    change dist ((T z : S) : B) ((T w : S) : B) ≤ (k : ℝ) * dist (z : B) (w : B)
    simpa only [dist_eq_norm] using hdiff z w
  obtain ⟨z, hz, _⟩ := hT.exists_fixedPoint (⟨0, by simpa using hρ⟩ : S) (edist_ne_top _ _)
  exact ⟨z, z.property, (congrArg Subtype.val hz).symm⟩

variable {E : Type*} [NormedField E] [NormedAlgebra E B]

/-- An approximate cube root of one admits a nearby exact root in any
complete commutative nonarchimedean algebra at the cubic contraction radius. -/
theorem exists_cube_root_near_one_algebra [CompleteSpace B]
    (hna : IsNonarchimedean (norm : B → ℝ)) (x : B) (s : E)
    (hs : (3 : E) * s = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hx : ‖x‖ ≤ 1) (hq : ‖x ^ 3 - 1‖ < 1)
    (hinit : ‖s‖ * ‖x ^ 3 - 1‖ ≤ ρ) (hcubic : ‖s‖ * ρ ^ 2 < 1) :
    ∃ y : B, ‖y - x‖ ≤ ρ ∧ y ^ 3 = 1 := by
  have hx3 : ‖x ^ 3‖ ≤ 1 := (norm_pow_le' _ (by norm_num)).trans
    (by simpa using pow_le_pow_left₀ (norm_nonneg x) hx 3)
  obtain ⟨z, hz, heq⟩ := hna.exists_cubic_fixedPoint_algebra
    (-(s • (x ^ 3 - 1))) (-(x ^ 3 - 1)) (-(x ^ 3)) (-(s • x ^ 3)) hρ
    (by simpa only [norm_neg, norm_smul] using hinit)
    (by simpa only [norm_neg] using hq)
    (by
      rw [norm_neg]
      exact (mul_le_mul_of_nonneg_right hx3 hρ).trans_lt (by simpa using hρ1))
    (by rw [norm_neg, norm_smul]
        exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hx3 (norm_nonneg s)) (sq_nonneg ρ)).trans_lt
          (by simpa using hcubic))
  have hsB : (3 : B) * algebraMap E B s = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using congrArg (algebraMap E B) hs
  simp only [Algebra.smul_def] at heq
  have hzero : 3 * z + (x ^ 3 - 1) + 3 * (x ^ 3 - 1) * z +
      3 * x ^ 3 * z ^ 2 + x ^ 3 * z ^ 3 = 0 := by
    linear_combination 3 * heq - (x ^ 3 - 1 + x ^ 3 * z ^ 3) * hsB
  refine ⟨x * (1 + z), ?_, ?_⟩
  · rw [show x * (1 + z) - x = x * z by ring]
    exact (norm_mul_le _ _).trans ((mul_le_mul hx hz (norm_nonneg _) (by norm_num)).trans
      (by simp))
  · linear_combination hzero

end IsNonarchimedean
