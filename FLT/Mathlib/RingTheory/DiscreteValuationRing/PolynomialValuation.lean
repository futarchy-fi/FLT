/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.DiscreteValuationRing.TotalRamification
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# No cancellation in short uniformizer expansions

Over a totally ramified DVR algebra of index `e`, the terms of a polynomial
of degree less than `e` have distinct valuations modulo `e`. Evaluation
therefore has valuation at most that of any nonzero term.
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]

/-- Nonzero base elements have mapped valuation divisible by the mapped uniformizer valuation. -/
theorem exists_addVal_map_eq_mul {π : R} (hπ : Irreducible π)
    {e : ℕ} (he : addVal S (algebraMap R S π) = e) {a : R} (ha : a ≠ 0) :
    ∃ n : ℕ, addVal S (algebraMap R S a) = (e * n : ℕ) := by
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
  refine ⟨n, ?_⟩
  rw [map_mul, map_pow, addVal_mul, addVal_pow,
    addVal_eq_zero_iff.mpr (u.isUnit.map (algebraMap R S)), zero_add, he]
  simp [nsmul_eq_mul, mul_comm]

/-- Terms below the ramification index have distinct finite valuations. -/
theorem uniformizer_term_values_distinct {π : R} (hπ : Irreducible π)
    {e : ℕ} (he : addVal S (algebraMap R S π) = e)
    {y : S} (hy : Irreducible y) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    {i j : ℕ} (hi : i < e) (hj : j < e) (hne : i ≠ j) :
    addVal S (algebraMap R S a * y ^ i) ≠
      addVal S (algebraMap R S b * y ^ j) := by
  obtain ⟨m, hm⟩ := exists_addVal_map_eq_mul hπ he ha
  obtain ⟨n, hn⟩ := exists_addVal_map_eq_mul hπ he hb
  rw [addVal_mul, addVal_mul, hm, hn, hy.addVal_pow, hy.addVal_pow,
    ← Nat.cast_add, ← Nat.cast_add, ne_eq, ENat.natCast_inj]
  intro h
  have := congrArg (· % e) h
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add,
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact hne this

/-- Evaluation of a polynomial shorter than the ramification index cannot
cancel its least-valuation term. -/
theorem addVal_aeval_le_term {π : R} (hπ : Irreducible π)
    {e : ℕ} (he : addVal S (algebraMap R S π) = e)
    {y : S} (hy : Irreducible y) (P : Polynomial R) (hdeg : P.natDegree < e)
    {j : ℕ} (hj : j < e) (hc : P.coeff j ≠ 0) :
    addVal S (Polynomial.aeval y P) ≤
      addVal S (algebraMap R S (P.coeff j) * y ^ j) := by
  classical
  let t : ℕ → S := fun i ↦ algebraMap R S (P.coeff i) * y ^ i
  obtain ⟨m, hm⟩ := exists_addVal_map_eq_mul hπ he hc
  have hjtop : addVal S (t j) ≠ ⊤ := by
    dsimp only [t]
    rw [addVal_mul, hm, hy.addVal_pow, ← Nat.cast_add]
    exact ENat.natCast_ne_top _
  obtain ⟨i, hi, hmin⟩ := (Finset.range e).exists_min_image
    (fun i ↦ addVal S (t i)) ⟨j, Finset.mem_range.mpr hj⟩
  have hitop : addVal S (t i) ≠ ⊤ :=
    ne_top_of_le_ne_top hjtop (hmin j (Finset.mem_range.mpr hj))
  have hic : P.coeff i ≠ 0 := by
    intro hz
    apply hitop
    simp [t, hz]
  have hs : addVal S (∑ k ∈ Finset.range e, t k) = addVal S (t i) := by
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hi]
    apply AddValuation.map_add_eq_of_lt_left
    apply AddValuation.map_lt_sum _ hitop
    intro k hk
    have hk' := Finset.mem_sdiff.mp hk
    have hki : k ≠ i := by simpa only [Finset.mem_singleton] using hk'.2
    apply lt_of_le_of_ne (hmin k hk'.1)
    by_cases hkc : P.coeff k = 0
    · simpa [t, hkc] using hitop
    · exact uniformizer_term_values_distinct hπ he hy hic hkc
        (Finset.mem_range.mp hi) (Finset.mem_range.mp hk'.1) hki.symm
  rw [Polynomial.aeval_eq_sum_range' hdeg y]
  simp only [Algebra.smul_def]
  exact hs.trans_le (hmin j (Finset.mem_range.mpr hj))

end IsDiscreteValuationRing
