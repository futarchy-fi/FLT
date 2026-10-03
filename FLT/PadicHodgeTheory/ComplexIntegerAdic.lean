/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicTilt
public import Mathlib.RingTheory.AdicCompletion.Topology

/-! # The actual integer ring of C_p is p-adically complete -/

@[expose] public noncomputable section
open scoped NNReal Topology
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The completed valuation agrees with the inherited norm. -/
theorem complex_valuation_coe (x : ℂ_[p]) : ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖ := by
  simpa only [Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding,
    Valuation.embedding_restrict] using
    (PadicComplex.norm_eq_norm p x).symm

/-- Each principal p-power ideal is the corresponding closed norm ball. -/
theorem complexInteger_powerIdeal (n : ℕ) :
    (((Ideal.span {(p : 𝓞_ℂ_[p])}) ^ n : Ideal 𝓞_ℂ_[p]) : Set 𝓞_ℂ_[p]) =
      Metric.closedBall 0 (((p : ℝ)⁻¹) ^ n) := by
  ext x
  rw [Ideal.span_singleton_pow]
  simp only [SetLike.mem_coe, Ideal.mem_span_singleton,
    (PadicComplexInt.integers p).dvd_iff_le, map_pow, map_natCast,
    Metric.mem_closedBall, dist_zero_right]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_pow, PadicComplex.valuation_p, one_div, NNReal.coe_inv,
    NNReal.coe_natCast, complex_valuation_coe]
  rfl

/-- The p-adic and metric topologies on the actual integer ring coincide. -/
theorem complexInteger_isAdic : IsAdic (Ideal.span {(p : 𝓞_ℂ_[p])}) := by
  have hp0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀
    (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  rw [isAdic_iff]
  constructor
  · intro n
    rw [complexInteger_powerIdeal]
    exact IsUltrametricDist.isOpen_closedBall _ (ne_of_gt (pow_pos hp0 n))
  · intro s hs
    obtain ⟨n, _, hn⟩ := (Metric.nhds_basis_closedBall_pow hp0 hp1).mem_iff.mp hs
    exact ⟨n, by simpa only [complexInteger_powerIdeal] using hn⟩

/-- The ring of integers is a closed, hence complete, subspace of C_p. -/
instance complexInteger_completeSpace : CompleteSpace 𝓞_ℂ_[p] :=
  (Valued.isClosed_valuationSubring ℂ_[p]).completeSpace_coe

/-- Actual completeness, needed to define the untilt and Fontaine theta maps. -/
instance complexInteger_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] :=
  (complexInteger_isAdic p).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

end PadicHodgeTheory
