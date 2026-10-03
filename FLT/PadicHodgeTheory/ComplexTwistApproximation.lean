/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexGaloisApproximation
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-! # Uniform approximation bounds for actual integral cyclotomic weights -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The original character, to an integer power, in the algebraic closure. -/
def padicCyclotomicWeight (σ : PadicGalois p) (n : ℤ) : PadicAlgCl p :=
  algebraMap ℚ_[p] (PadicAlgCl p)
    (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ^ n)

/-- Every positive or negative cyclotomic weight has norm one. -/
theorem padicCyclotomicWeight_norm (σ : PadicGalois p) (n : ℤ) :
    ‖padicCyclotomicWeight p σ n‖ = 1 := by
  rw [padicCyclotomicWeight, norm_algebraMap, norm_zpow,
    ← PadicInt.norm_def, PadicInt.norm_units, one_zpow, norm_one, mul_one]

/-- The weighted displacement is nonexpanding as the completed vector varies. -/
theorem complexTwist_displacement_sub_le (σ : PadicGalois p) (n : ℤ) (x y : ℂ_[p]) :
    ‖((padicCyclotomicWeight p σ n : ℂ_[p]) * complexGalois p σ x - x) -
      ((padicCyclotomicWeight p σ n : ℂ_[p]) * complexGalois p σ y - y)‖ ≤ ‖x - y‖ := by
  have he : ((padicCyclotomicWeight p σ n : ℂ_[p]) * complexGalois p σ x - x) -
      ((padicCyclotomicWeight p σ n : ℂ_[p]) * complexGalois p σ y - y) =
      (padicCyclotomicWeight p σ n : ℂ_[p]) * complexGalois p σ (x - y) - (x - y) := by
    rw [map_sub]; ring
  rw [he]
  simpa only [sub_eq_add_neg, norm_neg, norm_mul, PadicComplex.norm_extends,
    padicCyclotomicWeight_norm, one_mul, complexGalois_norm, max_self] using
    PadicComplex.isNonarchimedean p
      ((padicCyclotomicWeight p σ n : ℂ_[p]) * complexGalois p σ (x - y)) (-(x - y))

/-- A completed twist invariant has algebraic approximants with uniformly small weighted error. -/
theorem complexTwist_fixed_algebraic_approximation (n : ℤ) (x : ℂ_[p])
    (hx : ∀ σ : PadicGalois p,
      (padicCyclotomicWeight p σ n : ℂ_[p]) * complexGalois p σ x = x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : PadicAlgCl p, ‖(a : ℂ_[p]) - x‖ < ε ∧
      ∀ σ : PadicGalois p, ‖padicCyclotomicWeight p σ n * σ a - a‖ < ε := by
  obtain ⟨a, ha⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x hε
  rw [dist_eq_norm, norm_sub_rev] at ha
  refine ⟨a, ha, fun σ ↦ ?_⟩
  have h := complexTwist_displacement_sub_le p σ n (a : ℂ_[p]) x
  rw [hx σ, sub_self, sub_zero, complexGalois_coe,
    ← UniformSpace.Completion.coe_mul, ← UniformSpace.Completion.coe_sub,
    PadicComplex.norm_extends] at h
  exact h.trans_lt ha

end PadicHodgeTheory
