/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexAxDescent
public import FLT.PadicHodgeTheory.PadicAxEstimate

/-! # The fixed scalars in the actual completed algebraic closure

The arithmetic estimate is proved by degree descent. No analytic fixed-field
statement or uniform approximation estimate is an extra hypothesis.
-/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [hp : Fact p.Prime]

/-- Every fixed element of the original completed Galois action is a standard Q_p scalar. -/
theorem complexGalois_fixed_mem_range (x : ℂ_[p])
    (hx : ∀ σ : PadicGalois p, complexGalois p σ x = x) :
    x ∈ Set.range (algebraMap ℚ_[p] ℂ_[p]) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  exact complexGalois_fixed_mem_range_of_uniform_estimate p ((p : ℝ) ^ 2)
    (pow_pos hp' _) (fun a _ hr ha ↦ padicAx_exists_scalar p a hr.le ha) x hx

/-- The fixed elements of C_p are exactly the original Q_p image. -/
theorem complexGalois_fixed_iff_mem_range (x : ℂ_[p]) :
    (∀ σ : PadicGalois p, complexGalois p σ x = x) ↔
      x ∈ Set.range (algebraMap ℚ_[p] ℂ_[p]) := by
  refine ⟨complexGalois_fixed_mem_range p x, ?_⟩
  rintro ⟨a, rfl⟩ σ
  exact complexGalois_algebraMap p σ a

/-- Descent gives a unique scalar, since the original scalar map is injective. -/
theorem complexGalois_fixed_existsUnique_scalar (x : ℂ_[p])
    (hx : ∀ σ : PadicGalois p, complexGalois p σ x = x) :
    ∃! a : ℚ_[p], algebraMap ℚ_[p] ℂ_[p] a = x := by
  obtain ⟨a, ha⟩ := complexGalois_fixed_mem_range p x hx
  exact ⟨a, ha, fun b hb ↦ (algebraMap ℚ_[p] ℂ_[p]).injective (hb.trans ha.symm)⟩

end PadicHodgeTheory
