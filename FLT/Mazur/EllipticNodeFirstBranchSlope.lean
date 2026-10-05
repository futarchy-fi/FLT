/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeSameBranchSlope
public import FLT.Mazur.EllipticNodeSecantSlope
public import FLT.Mazur.EllipticNodeComponentLabel

/-!
# Actual slopes for ordered first-branch points

For unequal depths the divided first denominator is a unit; at equal depths
the divided second denominator is a unit. These give one integral slope
interface, with residue zero, including the tangent chart.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] {A : ValuationSubring K}
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- Ordered positive first-branch points have an actual integral slope with residue zero. -/
theorem exists_node_first_branch_slope
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hkw : v.depth ≤ w.depth) (hw : 2 * w.depth < n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) :
    ∃ l : A, l ∈ maximalIdeal A ∧
      (W.map (algebraMap A K)).toAffine.slope
        ((π ^ v.depth * v.a : A) : K) ((π ^ w.depth * w.a : A) : K)
        ((π ^ v.depth * v.b : A) : K) ((π ^ w.depth * w.b : A) : K) = (l : K) ∧
      ¬ (((π ^ v.depth * v.a : A) : K) = ((π ^ w.depth * w.a : A) : K) ∧
        ((π ^ v.depth * v.b : A) : K) = (W.map (algebraMap A K)).toAffine.negY
          ((π ^ w.depth * w.a : A) : K) ((π ^ w.depth * w.b : A) : K)) := by
  have hπ : π ∈ maximalIdeal A := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  obtain ⟨ha, _⟩ := node_point_branches_below_middle W D.uniformizer_ne_zero D.maximalIdeal_eq
    n v.depth hk (by omega) D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
    v.a v.b v.primitive v.equation
  rcases eq_or_lt_of_le hkw with he | he
  · obtain ⟨hc, _⟩ := node_point_branches_below_middle W D.uniformizer_ne_zero D.maximalIdeal_eq
      n w.depth (by omega) hw D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
      w.a w.b w.primitive w.equation
    obtain ⟨e₃, he₃, h3⟩ := exists_node_deep_factor D.maximalIdeal_eq v.depth
      (Ideal.pow_le_pow_right (by omega) D.a₃_mem)
    obtain ⟨e₄, he₄, h4⟩ := exists_node_deep_factor D.maximalIdeal_eq v.depth
      (Ideal.pow_le_pow_right (by omega) D.a₄_mem)
    have hu := node_same_branch_denominator_unit W D.a₁_unit hc hb hd he₃
    obtain ⟨l, hl, hy⟩ := exists_node_second_slope A W D.uniformizer_ne_zero v.depth
      v.a v.b w.a w.b e₃ e₄ h3 h4 hu v.nonsingular.1
      (by simpa only [he] using w.nonsingular.1)
    have hr := node_equal_depth_second_residue A W D.uniformizer_ne_zero hπ v.depth hk
      v.a v.b w.a w.b l e₃ e₄ D.a₂_mem he₃ he₄ h3 h4 v.nonsingular.1
      (by simpa only [he] using w.nonsingular.1) (fun h => hy h.2) hl
    have hl0 : residue A l = 0 := by
      simp only [(residue_eq_zero_iff _).mpr hb, (residue_eq_zero_iff _).mpr hd,
        zero_add, mul_zero, neg_zero] at hr
      exact (mul_eq_zero.mp hr).resolve_left
        (mul_ne_zero ((residue_ne_zero_iff_isUnit _).mpr D.a₁_unit)
          ((residue_ne_zero_iff_isUnit _).mpr hc))
    refine ⟨l, (residue_eq_zero_iff _).mp hl0, ?_, ?_⟩
    · simpa only [he] using hl
    · simpa only [he] using (show ¬ (_ ∧ _) from fun h => hy h.2)
  · let j := w.depth - v.depth
    have hj : 0 < j := by dsimp [j]; omega
    have hew : w.depth = v.depth + j := by dsimp [j]; omega
    obtain ⟨l, hl, hr⟩ := exists_node_secant_slope hπ ha j hj v.b w.a w.b
    have hl0 : residue A l = 0 := by
      rw [(residue_eq_zero_iff _).mpr hb] at hr
      exact (mul_eq_zero.mp hr).resolve_right ((residue_ne_zero_iff_isUnit _).mpr ha)
    refine ⟨l, (residue_eq_zero_iff _).mp hl0, ?_, ?_⟩
    · simpa only [hew] using node_secant_slope_eq A W D.uniformizer_ne_zero hπ ha
        v.depth j hj v.b w.a w.b l hl
    · rintro ⟨hx, _⟩
      have hxA : π ^ v.depth * v.a = π ^ (v.depth + j) * w.a := by
        simpa only [hew] using Subtype.ext hx
      have hz : π ^ v.depth * (v.a - π ^ j * w.a) = 0 := by
        rw [mul_sub, ← mul_assoc, ← pow_add, hxA, sub_self]
      exact mul_ne_zero (pow_ne_zero v.depth D.uniformizer_ne_zero)
        (node_secant_denominator_unit hπ ha j hj w.a).ne_zero hz

end FLT.Mazur
