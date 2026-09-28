/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Tactic.Abel

/-!
# Newton lifting with a bounded inverse and a Lipschitz remainder

This version of Newton's method works on a complete nonarchimedean normed
additive group, including finite products of a complete valued field.
It freezes an invertible linear approximation at the initial point and proves
existence and uniqueness by contraction on the prescribed closed ball.

The hypotheses explicitly separate the inverse bound from the nonlinear
remainder bound. In particular, an inverse bound alone does not supply the
stronger nonlinear estimate needed at Fontaine's three-halves threshold.
-/

@[expose] public noncomputable section

namespace NonarchimedeanNewton

open scoped NNReal

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]

/-- A bounded invertible additive approximation and a sufficiently small
Lipschitz remainder give a unique zero in the prescribed ball. Applied to
finite products of a valued field, this is a several-variable Newton lemma. -/
theorem existsUnique_root_of_linear_remainder_bound [CompleteSpace V]
    (hna : ∀ u v : V, ‖u + v‖ ≤ max ‖u‖ ‖v‖)
    (f : V → W) (x : V) (J : V ≃+ W) (B L : ℝ≥0) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hJ : ∀ w, ‖J.symm w‖ ≤ B * ‖w‖)
    (hf : B * ‖f x‖ ≤ ρ) (hk : B * L < 1)
    (hrem : ∀ z w : V, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖f (x + z) - f (x + w) - J (z - w)‖ ≤ L * ‖z - w‖) :
    ∃! y : V, ‖y - x‖ ≤ ρ ∧ f y = 0 := by
  let T : V → V := fun z ↦ z - J.symm (f (x + z))
  have hdiff (z w : V) (hz : ‖z‖ ≤ ρ) (hw : ‖w‖ ≤ ρ) :
      ‖T z - T w‖ ≤ (B * L : ℝ≥0) * ‖z - w‖ := by
    have he : T z - T w = -J.symm (f (x + z) - f (x + w) - J (z - w)) := by
      simp only [T, map_sub, AddEquiv.symm_apply_apply]
      abel
    rw [he, norm_neg]
    exact (hJ _).trans (by simpa only [NNReal.coe_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left (hrem z w hz hw) B.coe_nonneg)
  have hzero : ‖T 0‖ ≤ ρ := by simpa [T] using (hJ (f x)).trans hf
  have hmap (z : V) (hz : ‖z‖ ≤ ρ) : ‖T z‖ ≤ ρ := by
    have hn := hna (T z - T 0) (T 0)
    rw [sub_add_cancel] at hn
    refine hn.trans (max_le ?_ hzero)
    have hd := hdiff z 0 hz (by simpa using hρ)
    simp only [sub_zero] at hd
    exact hd.trans ((mul_le_mul_of_nonneg_left hz (B * L).coe_nonneg).trans
      (by simpa using mul_le_mul_of_nonneg_right (show (B * L : ℝ≥0) ≤ (1 : ℝ) from hk.le) hρ))
  let S := {z : V // ‖z‖ ≤ ρ}
  have hclosed : IsClosed {z : V | ‖z‖ ≤ ρ} := isClosed_le continuous_norm continuous_const
  let : CompleteSpace S := hclosed.completeSpace_coe
  let T' : S → S := fun z ↦ ⟨T z, hmap z z.property⟩
  have hT : ContractingWith (B * L) T' := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul fun z w ↦ ?_⟩
    change dist (T (z : V)) (T (w : V)) ≤ (B * L : ℝ≥0) * dist (z : V) (w : V)
    simpa only [dist_eq_norm] using hdiff z w z.property w.property
  obtain ⟨z, hz, _⟩ := hT.exists_fixedPoint (⟨0, by simpa using hρ⟩ : S) (edist_ne_top _ _)
  have he : T (z : V) = z := congrArg Subtype.val hz
  have hzroot : f (x + (z : V)) = 0 := by
    have hh : J.symm (f (x + (z : V))) = 0 := sub_eq_self.mp he
    exact J.symm.injective (hh.trans (map_zero J.symm).symm)
  refine ⟨x + z, ⟨by simpa using z.property, hzroot⟩, ?_⟩
  intro y hy
  let w : S := ⟨y - x, hy.1⟩
  have hw : Function.IsFixedPt T' w := by
    apply Subtype.ext
    change (y - x) - J.symm (f (x + (y - x))) = y - x
    rw [add_sub_cancel, hy.2, map_zero, sub_zero]
  have hwz : w = z := hT.fixedPoint_unique' hw hz
  have hv := congrArg Subtype.val hwz
  dsimp only [w] at hv
  rw [← hv]
  abel

end NonarchimedeanNewton
