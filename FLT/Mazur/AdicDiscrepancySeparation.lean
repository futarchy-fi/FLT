/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Filtration

/-!
# Finite adic discrepancies have an annihilator congruent to one

The finiteness hypothesis is over the ring supplying the scalar. Applying this
with the relation coordinate ring produces a relation scalar; it does not
produce a source scalar unless the discrepancy module is finite over the source.
-/

@[expose] public section
namespace FLT.Mazur.AdicDiscrepancySeparation
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [IsNoetherianRing R] [Module.Finite R M]

/-- A discrepancy in every positive adic order has an actual annihilating scalar. -/
theorem exists_annihilator (I : Ideal R) (x : M)
    (hx : ∀ n : ℕ, x ∈ (I ^ (n + 1) • ⊤ : Submodule R M)) :
    ∃ s : R, 1 - s ∈ I ∧ s • x = 0 := by
  have h : x ∈ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) := by
    rw [Submodule.mem_iInf]
    intro n
    cases n with
    | zero => simp
    | succ n => exact hx n
  obtain ⟨r, hr⟩ := (I.mem_iInf_smul_pow_eq_bot_iff x).mp h
  refine ⟨1 - r, ?_, ?_⟩
  · simpa only [sub_sub_cancel] using r.property
  · rw [sub_smul, one_smul, hr, sub_self]

/-- The constructed scalar avoids every proper ideal containing the adic ideal. -/
theorem exists_annihilator_outside (I P : Ideal R) (hIP : I ≤ P) (hP : P ≠ ⊤)
    (x : M) (hx : ∀ n : ℕ, x ∈ (I ^ (n + 1) • ⊤ : Submodule R M)) :
    ∃ s : R, s ∉ P ∧ 1 - s ∈ I ∧ s • x = 0 := by
  obtain ⟨s, hs, hx⟩ := exists_annihilator I x hx
  refine ⟨s, ?_, hs, hx⟩
  intro h
  exact hP (P.eq_top_iff_one.mpr (by simpa using P.add_mem (hIP hs) h))

/-- Local noetherian separation kills a discrepancy at every positive order. -/
theorem eq_zero_of_local [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) (x : M)
    (hx : ∀ n : ℕ, x ∈ (I ^ (n + 1) • ⊤ : Submodule R M)) : x = 0 := by
  apply (Submodule.mem_bot R).mp
  rw [← I.iInf_pow_smul_eq_bot_of_isLocalRing hI, Submodule.mem_iInf]
  intro n
  cases n with
  | zero => simp
  | succ n => exact hx n

/-- Ring-valued discrepancies retain their full ideal powers, including nilpotents. -/
theorem exists_ring_annihilator (I : Ideal R) (x : R)
    (hx : ∀ n : ℕ, x ∈ I ^ (n + 1)) :
    ∃ s : R, 1 - s ∈ I ∧ s * x = 0 := by
  apply exists_annihilator I x
  intro n
  simpa only [smul_eq_mul, ← Ideal.one_eq_top, mul_one] using hx n

end FLT.Mazur.AdicDiscrepancySeparation
