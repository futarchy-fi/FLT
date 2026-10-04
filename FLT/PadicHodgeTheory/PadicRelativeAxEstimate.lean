/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicRelativeAxDegreeStep

/-! # An unconditional uniform relative algebraic Ax estimate

Strong induction on the actual minimal-polynomial degree, using Hasse roots,
proves scalar approximation with the deliberately nonoptimal constant p squared.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [hp : Fact p.Prime] (E : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- Actual scalar approximation with the accumulated Hasse-derivative degree budget. -/
theorem padicRelativeAx_exists_scalar_degree_bound (a : PadicAlgCl p) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ σ : Gal(PadicAlgCl p/E), ‖σ a - a‖ ≤ r) :
    ∃ b : E, ‖a - algebraMap E (PadicAlgCl p) b‖ ≤
      axDegreeFactor p (minpoly E a).natDegree * r := by
  generalize hn : (minpoly E a).natDegree = n
  induction n using Nat.strong_induction_on generalizing a r with
  | h n ih =>
    have hpos : 0 < (minpoly E a).natDegree :=
      minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral a)
    by_cases hscalar : (minpoly E a).natDegree = 1
    · obtain ⟨b, hb⟩ := minpoly.natDegree_eq_one_iff.mp hscalar
      refine ⟨b, ?_⟩
      rw [hb, sub_self, norm_zero]
      exact mul_nonneg (zero_le_one.trans
        (axDegreeFactor_one_le hp.out.one_lt.le (by omega))) hr
    · have hn' : 1 < (minpoly E a).natDegree := by omega
      obtain ⟨b, d, hdeg, hd, hab, hdisp, hbudget⟩ := padicRelativeAx_degree_step p E a hr ha hn'
      have hd0 : 0 ≤ d := zero_le_one.trans hd
      obtain ⟨c, hc⟩ := ih (minpoly E b).natDegree (by omega)
        b (mul_nonneg hd0 hr) hdisp rfl
      have hfac : 1 ≤ axDegreeFactor p (minpoly E b).natDegree :=
        axDegreeFactor_one_le hp.out.one_lt.le
          (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral b))
      have hdle : d ≤ axDegreeFactor p n := by
        have := (mul_le_mul_of_nonneg_right hfac hd0).trans hbudget
        simpa only [one_mul, hn] using this
      have hcle : ‖b - algebraMap E (PadicAlgCl p) c‖ ≤ axDegreeFactor p n * r := by
        apply hc.trans
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by simpa only [hn] using hbudget) hr
      refine ⟨c, ?_⟩
      have he : a - algebraMap E (PadicAlgCl p) c =
          (a - b) + (b - algebraMap E (PadicAlgCl p) c) := by ring
      rw [he]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (hab.trans (mul_le_mul_of_nonneg_right hdle hr)) hcle)

/-- The uniform algebraic Ax estimate: the constant p squared is independent of the element. -/
theorem padicRelativeAx_exists_scalar (a : PadicAlgCl p) {r : ℝ} (hr : 0 ≤ r)
    (ha : ∀ σ : Gal(PadicAlgCl p/E), ‖σ a - a‖ ≤ r) :
    ∃ b : E, ‖a - algebraMap E (PadicAlgCl p) b‖ ≤ (p : ℝ) ^ 2 * r := by
  obtain ⟨b, hb⟩ := padicRelativeAx_exists_scalar_degree_bound p E a hr ha
  exact ⟨b, hb.trans (mul_le_mul_of_nonneg_right (axDegreeFactor_le_sq hp.out.one_lt.le) hr)⟩

end PadicHodgeTheory
