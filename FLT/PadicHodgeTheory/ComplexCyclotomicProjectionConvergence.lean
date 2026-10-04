/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicProjection

/-! # The bounded tower projections converge to the original vector -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Density, exact finite-level stabilization and the uniform bound give convergence. -/
theorem complexCyclotomicProjection_tendsto (x : complexCyclotomicClosure p) :
    Filter.Tendsto (fun n : ℕ ↦ complexCyclotomicProjection p n x) Filter.atTop
      (nhds (x : ℂ_[p])) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hden : 0 < (p : ℝ) + 1 := by positivity
  obtain ⟨b, hb⟩ := (complexCyclotomicInclusion_dense p).exists_dist_lt x (div_pos hε hden)
  obtain ⟨N, hN⟩ := complexCyclotomicProjection_eventually_eq p b
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnorm : ‖x - complexCyclotomicInclusion p b‖ < ε / ((p : ℝ) + 1) := by
    simpa only [dist_eq_norm] using hb
  have he : complexCyclotomicProjection p n x - (x : ℂ_[p]) =
      complexCyclotomicProjection p n (x - complexCyclotomicInclusion p b) -
        ((x - complexCyclotomicInclusion p b : complexCyclotomicClosure p) : ℂ_[p]) := by
    rw [map_sub, hN n hn]
    change _ = (_ - ((b : PadicAlgCl p) : ℂ_[p])) -
      ((x : ℂ_[p]) - ((b : PadicAlgCl p) : ℂ_[p]))
    ring
  rw [dist_eq_norm, he]
  calc
    _ ≤ ‖complexCyclotomicProjection p n (x - complexCyclotomicInclusion p b)‖ +
        ‖((x - complexCyclotomicInclusion p b : complexCyclotomicClosure p) : ℂ_[p])‖ :=
      norm_sub_le _ _
    _ ≤ p * ‖x - complexCyclotomicInclusion p b‖ + ‖x - complexCyclotomicInclusion p b‖ :=
      add_le_add (complexCyclotomicProjection_norm_le p n _) le_rfl
    _ = ((p : ℝ) + 1) * ‖x - complexCyclotomicInclusion p b‖ := by ring
    _ < ε := (mul_lt_mul_of_pos_left hnorm hden).trans_eq (mul_div_cancel₀ ε hden.ne')

end PadicHodgeTheory
