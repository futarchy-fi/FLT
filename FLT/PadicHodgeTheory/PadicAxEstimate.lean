/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicAxDegreeStep

/-! # An unconditional uniform algebraic Ax estimate

Strong induction on the actual minimal-polynomial degree, using Hasse roots,
proves scalar approximation with the deliberately nonoptimal constant p squared.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [hp : Fact p.Prime]

/-- Actual scalar approximation with the accumulated Hasse-derivative degree budget. -/
theorem padicAx_exists_scalar_degree_bound (a : PadicAlgCl p) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ σ : PadicGalois p, ‖σ a - a‖ ≤ r) :
    ∃ b : ℚ_[p], ‖a - algebraMap ℚ_[p] (PadicAlgCl p) b‖ ≤
      axDegreeFactor p (minpoly ℚ_[p] a).natDegree * r := by
  generalize hn : (minpoly ℚ_[p] a).natDegree = n
  induction n using Nat.strong_induction_on generalizing a r with
  | h n ih =>
    have hpos : 0 < (minpoly ℚ_[p] a).natDegree :=
      minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral a)
    by_cases hscalar : (minpoly ℚ_[p] a).natDegree = 1
    · obtain ⟨b, hb⟩ := minpoly.natDegree_eq_one_iff.mp hscalar
      refine ⟨b, ?_⟩
      rw [hb, sub_self, norm_zero]
      exact mul_nonneg (zero_le_one.trans
        (axDegreeFactor_one_le hp.out.one_lt.le (by omega))) hr
    · have hn' : 1 < (minpoly ℚ_[p] a).natDegree := by omega
      obtain ⟨b, d, hdeg, hd, hab, hdisp, hbudget⟩ := padicAx_degree_step p a hr ha hn'
      have hd0 : 0 ≤ d := zero_le_one.trans hd
      obtain ⟨c, hc⟩ := ih (minpoly ℚ_[p] b).natDegree (by omega)
        b (mul_nonneg hd0 hr) hdisp rfl
      have hfac : 1 ≤ axDegreeFactor p (minpoly ℚ_[p] b).natDegree :=
        axDegreeFactor_one_le hp.out.one_lt.le
          (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral b))
      have hdle : d ≤ axDegreeFactor p n := by
        have := (mul_le_mul_of_nonneg_right hfac hd0).trans hbudget
        simpa only [one_mul, hn] using this
      have hcle : ‖b - algebraMap ℚ_[p] (PadicAlgCl p) c‖ ≤ axDegreeFactor p n * r := by
        apply hc.trans
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by simpa only [hn] using hbudget) hr
      refine ⟨c, ?_⟩
      have he : a - algebraMap ℚ_[p] (PadicAlgCl p) c =
          (a - b) + (b - algebraMap ℚ_[p] (PadicAlgCl p) c) := by ring
      rw [he]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (hab.trans (mul_le_mul_of_nonneg_right hdle hr)) hcle)

/-- The uniform algebraic Ax estimate: the constant p squared is independent of the element. -/
theorem padicAx_exists_scalar (a : PadicAlgCl p) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ σ : PadicGalois p, ‖σ a - a‖ ≤ r) :
    ∃ b : ℚ_[p], ‖a - algebraMap ℚ_[p] (PadicAlgCl p) b‖ ≤ (p : ℝ) ^ 2 * r := by
  obtain ⟨b, hb⟩ := padicAx_exists_scalar_degree_bound p a hr ha
  exact ⟨b, hb.trans (mul_le_mul_of_nonneg_right (axDegreeFactor_le_sq hp.out.one_lt.le) hr)⟩

end PadicHodgeTheory
