/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.AdicCompletion.Topology

/-! # Continuity of integral p-adic scalar maps into adic rings -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The standard topology on Z_p is precisely its p-adic ideal topology. -/
theorem padicInt_standard_isAdic : IsAdic (Ideal.span {(p : ℤ_[p])}) := by
  have hball (n : ℕ) :
      (((Ideal.span {(p : ℤ_[p])}) ^ n : Ideal ℤ_[p]) : Set ℤ_[p]) =
        Metric.closedBall 0 (((p : ℝ)⁻¹) ^ n) := by
    ext x
    simp only [Ideal.span_singleton_pow, SetLike.mem_coe, Metric.mem_closedBall,
      dist_zero_right, ← PadicInt.norm_le_pow_iff_mem_span_pow, zpow_neg,
      zpow_natCast, inv_pow]
  have hp0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀
    (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  rw [isAdic_iff]
  constructor
  · intro n
    rw [hball]
    exact IsUltrametricDist.isOpen_closedBall _ (ne_of_gt (pow_pos hp0 n))
  · intro s hs
    obtain ⟨n, _, hn⟩ := (Metric.nhds_basis_closedBall_pow hp0 hp1).mem_iff.mp hs
    exact ⟨n, by simpa only [hball] using hn⟩

/-- Every unital Z_p map into a p-adic topological ring is continuous. -/
theorem padicInt_hom_continuous {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (hR : IsAdic (Ideal.span {(p : R)})) (f : ℤ_[p] →+* R) :
    Continuous f := by
  apply continuous_of_continuousAt_zero f
  rw [ContinuousAt, map_zero]
  apply ((padicInt_standard_isAdic p).hasBasis_nhds_zero.tendsto_iff
    hR.hasBasis_nhds_zero).mpr
  intro n _
  refine ⟨n, trivial, ?_⟩
  intro a ha
  simp only [SetLike.mem_coe, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha ⊢
  simpa only [map_pow, map_natCast] using map_dvd f ha

end PadicHodgeTheory
