/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexGaloisAction

/-! # Uniform displacement bounds for algebraic approximants in C_p -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Moving the vector changes its Galois displacement by at most the approximation error. -/
theorem complexGalois_displacement_sub_le (σ : PadicGalois p) (x y : ℂ_[p]) :
    ‖(complexGalois p σ x - x) - (complexGalois p σ y - y)‖ ≤ ‖x - y‖ := by
  have he : (complexGalois p σ x - x) - (complexGalois p σ y - y) =
      complexGalois p σ (x - y) - (x - y) := by rw [map_sub]; ring
  rw [he]
  simpa only [sub_eq_add_neg, norm_neg, complexGalois_norm, max_self] using
    PadicComplex.isNonarchimedean p (complexGalois p σ (x - y)) (-(x - y))

/-- The same approximation controls every automorphism, with no group-dependent constant. -/
theorem complexGalois_displacement_le (σ : PadicGalois p) (x y : ℂ_[p]) :
    ‖complexGalois p σ x - x‖ ≤ max ‖x - y‖ ‖complexGalois p σ y - y‖ := by
  calc
    _ = ‖((complexGalois p σ x - x) - (complexGalois p σ y - y)) +
        (complexGalois p σ y - y)‖ := by congr 1; ring
    _ ≤ max ‖(complexGalois p σ x - x) - (complexGalois p σ y - y)‖
        ‖complexGalois p σ y - y‖ := PadicComplex.isNonarchimedean p _ _
    _ ≤ _ := max_le_max (complexGalois_displacement_sub_le p σ x y) le_rfl

/-- A fixed completed vector has algebraic approximants with uniformly small displacement. -/
theorem complexGalois_fixed_algebraic_approximation (x : ℂ_[p])
    (hx : ∀ σ : PadicGalois p, complexGalois p σ x = x) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : PadicAlgCl p, ‖(a : ℂ_[p]) - x‖ < ε ∧
      ∀ σ : PadicGalois p, ‖σ a - a‖ < ε := by
  obtain ⟨a, ha⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x hε
  rw [dist_eq_norm, norm_sub_rev] at ha
  refine ⟨a, ha, fun σ ↦ ?_⟩
  have h := complexGalois_displacement_le p σ (a : ℂ_[p]) x
  rw [hx σ, sub_self, norm_zero, max_eq_left (norm_nonneg _)] at h
  have he : ‖complexGalois p σ (a : ℂ_[p]) - (a : ℂ_[p])‖ = ‖σ a - a‖ := by
    rw [complexGalois_coe, ← UniformSpace.Completion.coe_sub]
    exact PadicComplex.norm_extends p _
  rw [he] at h
  exact h.trans_lt ha

end PadicHodgeTheory
