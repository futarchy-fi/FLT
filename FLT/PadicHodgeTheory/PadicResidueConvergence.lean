/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicScalarTopology
public import Mathlib.NumberTheory.Padics.RingHoms

/-! # Natural representatives of p-adic residues converge -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The natural residue representative differs from its p-adic integer by a p^n multiple. -/
theorem padicResidue_difference_mem (x : ℤ_[p]) (n : ℕ) :
    ((x.toZModPow n).val : ℤ_[p]) - x ∈ Ideal.span {(p : ℤ_[p])} ^ n := by
  rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow]
  change PadicInt.toZModPow n (((x.toZModPow n).val : ℤ_[p]) - x) = 0
  simp only [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]

/-- Natural representatives converge in the standard topology on Z_p. -/
theorem padicResidue_tendsto (x : ℤ_[p]) :
    Filter.Tendsto (fun n ↦ ((x.toZModPow n).val : ℤ_[p])) Filter.atTop (nhds x) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply (padicInt_standard_isAdic p).hasBasis_nhds_zero.tendsto_right_iff.mpr
  intro k _
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  exact Ideal.pow_le_pow_right hn (padicResidue_difference_mem p x n)

/-- The representatives also converge after the standard inclusion into Q_p. -/
theorem padicResidue_tendsto_rational (x : ℤ_[p]) :
    Filter.Tendsto (fun n ↦ ((x.toZModPow n).val : ℚ_[p])) Filter.atTop (nhds (x : ℚ_[p])) := by
  have h := (PadicInt.isOpenEmbedding_coe (p := p)).continuous.continuousAt.tendsto.comp
    (padicResidue_tendsto p x)
  exact h

end PadicHodgeTheory
