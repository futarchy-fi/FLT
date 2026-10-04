/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicRelativeAxEstimate
public import FLT.PadicHodgeTheory.ComplexGaloisApproximation

/-! # Relative Ax descent into the closure of an actual intermediate field -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [hp : Fact p.Prime] (E : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- A relatively fixed completed vector has uniformly almost-fixed algebraic approximants. -/
theorem complexRelativeGalois_fixed_approximation (x : ℂ_[p])
    (hx : ∀ σ : Gal(PadicAlgCl p/E), complexGalois p (σ.restrictScalars ℚ_[p]) x = x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : PadicAlgCl p, ‖(a : ℂ_[p]) - x‖ < ε ∧
      ∀ σ : Gal(PadicAlgCl p/E), ‖σ a - a‖ < ε := by
  obtain ⟨a, ha⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x hε
  rw [dist_eq_norm, norm_sub_rev] at ha
  refine ⟨a, ha, fun σ ↦ ?_⟩
  have h := complexGalois_displacement_le p (σ.restrictScalars ℚ_[p]) (a : ℂ_[p]) x
  rw [hx σ, sub_self, norm_zero, max_eq_left (norm_nonneg _)] at h
  have he : ‖complexGalois p (σ.restrictScalars ℚ_[p]) (a : ℂ_[p]) - (a : ℂ_[p])‖ =
      ‖σ a - a‖ := by
    rw [complexGalois_coe, ← UniformSpace.Completion.coe_sub]
    exact PadicComplex.norm_extends p _
  rw [he] at h
  exact h.trans_lt ha

/-- Relative invariants descend to the closure of the actual intermediate field, unconditionally. -/
theorem complexRelativeGalois_fixed_mem_closure (x : ℂ_[p])
    (hx : ∀ σ : Gal(PadicAlgCl p/E), complexGalois p (σ.restrictScalars ℚ_[p]) x = x) :
    x ∈ closure (Set.range (fun b : E ↦ ((b : PadicAlgCl p) : ℂ_[p]))) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let C : ℝ := (p : ℝ) ^ 2
  have hC : 0 < C := pow_pos (by exact_mod_cast hp.out.pos) _
  have hden : 0 < C + 1 := by linarith
  have hδ : 0 < ε / (C + 1) := div_pos hε hden
  have hsmall : ε / (C + 1) < ε := div_lt_self hε (by linarith)
  have heq : (C + 1) * (ε / (C + 1)) = ε := mul_div_cancel₀ ε hden.ne'
  have hCsmall : C * (ε / (C + 1)) < ε := by nlinarith
  obtain ⟨a, ha, hσ⟩ := complexRelativeGalois_fixed_approximation p E x hx hδ
  obtain ⟨b, hb⟩ := padicRelativeAx_exists_scalar p E a hδ.le (fun σ ↦ (hσ σ).le)
  refine ⟨((b : PadicAlgCl p) : ℂ_[p]), ⟨b, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  have he : ‖(a : ℂ_[p]) - ((b : PadicAlgCl p) : ℂ_[p])‖ =
      ‖a - algebraMap E (PadicAlgCl p) b‖ := by
    rw [← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends]
    rfl
  calc
    _ = ‖(x - (a : ℂ_[p])) + ((a : ℂ_[p]) - ((b : PadicAlgCl p) : ℂ_[p]))‖ := by
      congr 1; ring
    _ ≤ max ‖x - (a : ℂ_[p])‖ ‖(a : ℂ_[p]) - ((b : PadicAlgCl p) : ℂ_[p])‖ :=
      PadicComplex.isNonarchimedean p _ _
    _ < ε := by
      rw [max_lt_iff, norm_sub_rev x, he]
      exact ⟨ha.trans hsmall, hb.trans_lt hCsmall⟩

/-- Every vector in that closure is fixed by the original completed relative action. -/
theorem complexRelativeGalois_fixed_of_mem_closure (x : ℂ_[p])
    (hx : x ∈ closure (Set.range (fun b : E ↦ ((b : PadicAlgCl p) : ℂ_[p]))))
    (σ : Gal(PadicAlgCl p/E)) : complexGalois p (σ.restrictScalars ℚ_[p]) x = x := by
  apply closure_minimal ?_ (isClosed_eq (complexGalois_isometry p _).continuous continuous_id) hx
  rintro _ ⟨b, rfl⟩
  change complexGalois p (σ.restrictScalars ℚ_[p]) ((b : PadicAlgCl p) : ℂ_[p]) = _
  rw [complexGalois_coe]
  exact congrArg (fun a : PadicAlgCl p ↦ (a : ℂ_[p])) (σ.commutes b)

end PadicHodgeTheory
