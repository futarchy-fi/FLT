/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexGaloisAction
public import Mathlib.Analysis.Normed.Group.Ultra

/-! # Orthogonality from a p-adic uniformizer norm -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [hp : Fact p.Prime]

/-- Clearing the uniformizer denominator expresses a term norm as an integral p-power. -/
theorem padic_uniformizer_term_norm_pow (u : PadicAlgCl p) (e : ℕ)
    (hu : ‖u‖ ^ e = (p : ℝ)⁻¹) (a : ℚ_[p]) (ha : a ≠ 0) (i : ℕ) :
    ‖algebraMap ℚ_[p] (PadicAlgCl p) a * u ^ i‖ ^ e =
      (p : ℝ) ^ (-(a.valuation * (e : ℤ)) - (i : ℤ)) := by
  rw [norm_mul, norm_algebraMap, norm_one, mul_one, norm_pow, mul_pow,
    show (‖u‖ ^ i) ^ e = (‖u‖ ^ e) ^ i by rw [← pow_mul, Nat.mul_comm, pow_mul], hu,
    Padic.norm_eq_zpow_neg_valuation ha, ← zpow_natCast (n := e), ← zpow_mul,
    inv_pow, ← zpow_natCast (n := i), ← zpow_neg,
    ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero : (p : ℝ) ≠ 0)]
  congr 1
  ring

/-- Distinct powers below the ramification degree have distinct nonzero term norms. -/
theorem padic_uniformizer_term_norm_ne (u : PadicAlgCl p) (e : ℕ)
    (hu : ‖u‖ ^ e = (p : ℝ)⁻¹) (a b : ℚ_[p]) (ha : a ≠ 0) (hb : b ≠ 0)
    {i j : ℕ} (hi : i < e) (hj : j < e) (hij : i ≠ j) :
    ‖algebraMap ℚ_[p] (PadicAlgCl p) a * u ^ i‖ ≠
      ‖algebraMap ℚ_[p] (PadicAlgCl p) b * u ^ j‖ := by
  intro h
  have he := congrArg (fun t : ℝ ↦ t ^ e) h
  rw [padic_uniformizer_term_norm_pow p u e hu a ha,
    padic_uniformizer_term_norm_pow p u e hu b hb] at he
  have hex : -(a.valuation * (e : ℤ)) - (i : ℤ) =
      -(b.valuation * (e : ℤ)) - (j : ℤ) :=
    (zpow_right_inj₀ (by exact_mod_cast hp.out.pos)
      (by exact_mod_cast hp.out.ne_one)).mp he
  have hdiv : (e : ℤ) ∣ (i : ℤ) - (j : ℤ) :=
    ⟨b.valuation - a.valuation, by nlinarith [hex]⟩
  have hm : (i : ℤ) % (e : ℤ) = (j : ℤ) % (e : ℤ) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hdiv)
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast hi),
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast hj)] at hm
  exact hij (by exact_mod_cast hm)

/-- Each uniformizer term is bounded by the norm of the whole finite expansion. -/
theorem padic_uniformizer_term_le_sum (u : PadicAlgCl p) (e : ℕ)
    (hu : ‖u‖ ^ e = (p : ℝ)⁻¹) (a : Fin e → ℚ_[p]) (i : Fin e) :
    ‖algebraMap ℚ_[p] (PadicAlgCl p) (a i) * u ^ (i : ℕ)‖ ≤
      ‖∑ j : Fin e, algebraMap ℚ_[p] (PadicAlgCl p) (a j) * u ^ (j : ℕ)‖ := by
  classical
  let s := Finset.univ.filter (fun j ↦ a j ≠ 0)
  have hsum : ∑ j ∈ s, algebraMap ℚ_[p] (PadicAlgCl p) (a j) * u ^ (j : ℕ) =
      ∑ j : Fin e, algebraMap ℚ_[p] (PadicAlgCl p) (a j) * u ^ (j : ℕ) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    simp [hj]
  by_cases hai : a i = 0
  · simp [hai]
  have hi : i ∈ s := by simp [s, hai]
  rw [← hsum, IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne ⟨i, hi⟩]
  · exact Finset.le_sup' (fun j ↦ ‖algebraMap ℚ_[p] (PadicAlgCl p) (a j) * u ^ (j : ℕ)‖) hi
  · intro j hj k hk hjk
    exact padic_uniformizer_term_norm_ne p u e hu (a j) (a k)
      (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2 j.isLt k.isLt
      (fun h ↦ hjk (Fin.ext h))

end PadicHodgeTheory
