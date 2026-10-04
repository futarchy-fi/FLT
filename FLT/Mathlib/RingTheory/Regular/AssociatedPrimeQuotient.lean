/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Regular.RegularSequence

/-! # Associated primes grow strictly across a regular quotient -/

@[expose] public section

open scoped Pointwise

namespace RingTheory.Sequence

open Submodule IsLocalRing

variable {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A nonzero element has finite divisibility by an element of the maximal ideal. -/
theorem exists_notMem_pow_smul_top {x : R} (hx : x ∈ maximalIdeal R) {m : M} (hm : m ≠ 0) :
    ∃ n : ℕ, m ∉ x ^ n • (⊤ : Submodule R M) := by
  by_contra! h
  have hI : Ideal.span {x} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  have hsep := (Ideal.span {x}).iInf_pow_smul_eq_bot_of_isLocalRing (M := M) hI
  apply hm
  have hmem : m ∈ ⨅ n : ℕ, (Ideal.span {x}) ^ n • (⊤ : Submodule R M) := by
    apply (mem_iInf _).mpr
    intro n
    simpa only [Ideal.span_singleton_pow, ideal_span_singleton_smul] using h n
  simpa only [hsep, mem_bot] using hmem

omit [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M] in
/-- Cancel powers of a regular element until a witness survives in the quotient. -/
theorem exists_colon_eq_notMem_smul {x : R} (hx : IsSMulRegular M x) {m : M} {n : ℕ}
    (hm : m ∉ x ^ n • (⊤ : Submodule R M)) :
    ∃ y : M, (⊥ : Submodule R M).colon {y} = (⊥ : Submodule R M).colon {m} ∧
      y ∉ x • (⊤ : Submodule R M) := by
  induction n generalizing m with
  | zero => simp at hm
  | succ n ih =>
    by_cases hdiv : m ∈ x • (⊤ : Submodule R M)
    · obtain ⟨z, _, hz⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hdiv
      have hznot : z ∉ x ^ n • (⊤ : Submodule R M) := by
        intro hzmem
        apply hm
        rw [← hz, pow_succ', mul_smul]
        exact smul_mem_pointwise_smul z x _ hzmem
      obtain ⟨y, hy, hyn⟩ := ih hznot
      refine ⟨y, hy.trans ?_, hyn⟩
      ext r
      simp only [mem_colon_singleton, mem_bot, ← hz]
      rw [smul_comm]
      exact ⟨fun h ↦ by rw [h, smul_zero], hx.right_eq_zero_of_smul⟩
    · exact ⟨m, rfl, hdiv⟩

/-- Each associated prime lies strictly below an associated prime after a regular quotient. -/
theorem exists_associatedPrime_quotSMulTop_gt {p : Ideal R} (hp : IsAssociatedPrime p M)
    {x : R} (hx : IsSMulRegular M x) (hm : x ∈ maximalIdeal R) :
    ∃ q : Ideal R, IsAssociatedPrime q (QuotSMulTop x M) ∧ p < q := by
  obtain ⟨hp', m, hpm⟩ := isAssociatedPrime_iff.mp hp
  have hm0 : m ≠ 0 := by
    intro h
    apply hp'.ne_top
    rw [hpm, h]
    ext r
    simp [mem_colon_singleton]
  obtain ⟨n, hn⟩ := exists_notMem_pow_smul_top hm hm0
  obtain ⟨y, hy, hyn⟩ := exists_colon_eq_notMem_smul hx hn
  have hpy : p = (⊥ : Submodule R M).colon {y} := hpm.trans hy.symm
  let z : QuotSMulTop x M := Submodule.Quotient.mk y
  have hz : z ≠ 0 := by
    intro hz
    exact hyn ((Submodule.Quotient.mk_eq_zero _).mp hz)
  obtain ⟨q, hq, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R z hz
  have hpq : p ≤ q := by
    apply le_trans _ hle
    intro r hr
    rw [hpy, mem_colon_singleton, mem_bot] at hr
    rw [mem_colon_singleton, mem_bot]
    change Submodule.Quotient.mk (r • y) = 0
    rw [hr, Submodule.Quotient.mk_zero]
  have hxq : x ∈ q := hle (by
    rw [mem_colon_singleton, mem_bot]
    change Submodule.Quotient.mk (x • y) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (smul_mem_pointwise_smul _ _ _ mem_top))
  have hxp : x ∉ p := by
    intro hxp
    rw [hpy, mem_colon_singleton, mem_bot] at hxp
    have hy0 := hx.right_eq_zero_of_smul hxp
    exact hyn (hy0 ▸ zero_mem _)
  exact ⟨q, hq, lt_of_le_of_ne hpq (fun h ↦ hxp (h ▸ hxq))⟩

end RingTheory.Sequence
