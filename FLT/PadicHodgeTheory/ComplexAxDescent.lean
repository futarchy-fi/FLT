/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexGaloisApproximation
public import FLT.PadicHodgeTheory.ComplexScalarClosed

/-! # Completion descent from an explicit uniform algebraic approximation estimate

This proves the completion step, conditional on a uniform algebraic estimate.
The arithmetic estimate is an explicit hypothesis here and is not proved by
finite-orbit averaging, whose loss depends on the orbit cardinality.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- A uniform algebraic displacement estimate suffices for descent of completed fixed vectors. -/
theorem complexGalois_fixed_mem_range_of_uniform_estimate
    (C : ℝ) (hC : 0 < C)
    (hestimate : ∀ (a : PadicAlgCl p) (r : ℝ), 0 < r →
      (∀ σ : PadicGalois p, ‖σ a - a‖ ≤ r) →
      ∃ b : ℚ_[p], ‖a - algebraMap ℚ_[p] (PadicAlgCl p) b‖ ≤ C * r)
    (x : ℂ_[p]) (hx : ∀ σ : PadicGalois p, complexGalois p σ x = x) :
    x ∈ Set.range (algebraMap ℚ_[p] ℂ_[p]) := by
  apply (complexScalar_mem_iff_approximation p x).mpr
  intro ε hε
  have hden : 0 < C + 1 := by linarith
  have hδ : 0 < ε / (C + 1) := div_pos hε hden
  have hsmall : ε / (C + 1) < ε := div_lt_self hε (by linarith)
  have heq : (C + 1) * (ε / (C + 1)) = ε := mul_div_cancel₀ ε hden.ne'
  have hCsmall : C * (ε / (C + 1)) < ε := by nlinarith
  obtain ⟨a, ha, hσ⟩ := complexGalois_fixed_algebraic_approximation p x hx hδ
  obtain ⟨b, hb⟩ := hestimate a (ε / (C + 1)) hδ (fun σ ↦ (hσ σ).le)
  have he : ‖(a : ℂ_[p]) - algebraMap ℚ_[p] ℂ_[p] b‖ =
      ‖a - algebraMap ℚ_[p] (PadicAlgCl p) b‖ := by
    change ‖(a : ℂ_[p]) - ((algebraMap ℚ_[p] (PadicAlgCl p) b : PadicAlgCl p) : ℂ_[p])‖ = _
    rw [← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends]
  refine ⟨b, ?_⟩
  calc
    ‖x - algebraMap ℚ_[p] ℂ_[p] b‖ =
        ‖(x - (a : ℂ_[p])) + ((a : ℂ_[p]) - algebraMap ℚ_[p] ℂ_[p] b)‖ := by
      congr 1; ring
    _ ≤ max ‖x - (a : ℂ_[p])‖ ‖(a : ℂ_[p]) - algebraMap ℚ_[p] ℂ_[p] b‖ :=
      PadicComplex.isNonarchimedean p _ _
    _ < ε := by
      rw [max_lt_iff, norm_sub_rev x, he]
      exact ⟨ha.trans hsmall, hb.trans_lt hCsmall⟩

end PadicHodgeTheory
