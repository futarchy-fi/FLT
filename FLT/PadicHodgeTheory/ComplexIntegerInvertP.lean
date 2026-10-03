/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexIntegerAdic
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Inverting p in the actual integer ring gives C_p -/

@[expose] public noncomputable section
open scoped NNReal Topology
open Filter
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The norm of p in the completed field is strictly smaller than one. -/
theorem complex_norm_prime_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [← complex_valuation_coe, PadicComplex.valuation_p]
  simp only [one_div, NNReal.coe_inv, NNReal.coe_natCast]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

/-- A sufficiently large power of p clears the denominator of any completed element. -/
theorem complexInteger_clear_denominator (x : ℂ_[p]) :
    ∃ n : ℕ, x * (p : ℂ_[p]) ^ n ∈ PadicComplexInt p := by
  have ht : Tendsto (fun n : ℕ ↦ ‖x * (p : ℂ_[p]) ^ n‖) atTop (𝓝 0) := by
    simp only [norm_mul, norm_pow]
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : ℂ_[p]))
        (complex_norm_prime_lt_one p)).const_mul ‖x‖
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
  refine ⟨n, ?_⟩
  change Valued.v (x * (p : ℂ_[p]) ^ n) ≤ (1 : ℝ≥0)
  rw [← NNReal.coe_le_coe, complex_valuation_coe]
  exact hn.le

/-- The original inclusion O_C → C_p is a localization away from p. -/
instance instIsLocalizationAwayComplex : IsLocalization.Away (p : 𝓞_ℂ_[p]) ℂ_[p] := by
  apply IsLocalization.Away.mk
  · rw [map_natCast, isUnit_iff_ne_zero]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  · intro x
    obtain ⟨n, hn⟩ := complexInteger_clear_denominator p x
    refine ⟨n, ⟨x * (p : ℂ_[p]) ^ n, hn⟩, ?_⟩
    rw [map_natCast]
    rfl
  · intro a b h
    have he : a = b := Subtype.ext h
    exact ⟨0, by rw [he]⟩

/-- The canonical localization equivalence retains the actual completed field. -/
def complexIntegerInvertPEquiv : Localization.Away (p : 𝓞_ℂ_[p]) ≃ₐ[𝓞_ℂ_[p]] ℂ_[p] :=
  IsLocalization.algEquiv (Submonoid.powers (p : 𝓞_ℂ_[p])) _ _

/-- The equivalence is the original inclusion on integers. -/
theorem complexIntegerInvertPEquiv_algebraMap (x : 𝓞_ℂ_[p]) :
    complexIntegerInvertPEquiv p
      (algebraMap 𝓞_ℂ_[p] (Localization.Away (p : 𝓞_ℂ_[p])) x) = (x : ℂ_[p]) :=
  (complexIntegerInvertPEquiv p).commutes x

end PadicHodgeTheory
