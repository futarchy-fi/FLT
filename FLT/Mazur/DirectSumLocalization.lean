/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.DirectSum.Module

/-!
# Localization of an arbitrary direct sum

A finite-support section admits one denominator for all its components.
Thus the direct sum of the original localization maps is itself localization;
no finite bound on the set of degrees is imposed.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.DirectSumLocalization

variable {R : Type*} [CommRing R] {ι : Type*}
variable {M N : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
variable [∀ i, Module R (M i)] [∀ i, Module R (N i)]
variable (r : R) (f : ∀ i, M i →ₗ[R] N i) [∀ i, IsLocalizedModule.Away r (f i)]

include f in
/-- Scalar multiplication remains invertible on the full direct sum of localized modules. -/
lemma scalar_isUnit : IsUnit (algebraMap R (Module.End R (⨁ i, N i)) r) := by
  let e (i : ι) : N i ≃ₗ[R] N i := LinearEquiv.ofBijective
    (algebraMap R (Module.End R (N i)) r)
    ((Module.End.isUnit_iff _).mp (IsLocalizedModule.Away.isUnit_algebraMap (f i) r))
  apply (Module.End.isUnit_iff _).mpr
  exact (DirectSum.congrLinearEquiv e).bijective

/-- One scalar power clears every component of a finite-support local section. -/
lemma exists_numerator (s : ⨁ i, N i) :
    ∃ (n : ℕ) (t : ⨁ i, M i), r ^ n • s = DirectSum.lmap f t := by
  classical
  induction s using DirectSum.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | of i s =>
    obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj (f i) r s
    exact ⟨n, DirectSum.of M i t, by simp only [← DirectSum.of_smul,
      DirectSum.lmap_of, ht]⟩
  | add s t hs ht =>
    obtain ⟨a, x, hx⟩ := hs
    obtain ⟨b, y, hy⟩ := ht
    refine ⟨a + b, r ^ b • x + r ^ a • y, ?_⟩
    rw [smul_add, map_add, map_smul, map_smul, ← hx, ← hy]
    congr 1
    · rw [← mul_smul, ← pow_add, Nat.add_comm]
    · rw [← mul_smul, ← pow_add]

/-- A section with zero localization is killed by one power across its finite support. -/
lemma exists_annihilator (s : ⨁ i, M i) (hs : DirectSum.lmap f s = 0) :
    ∃ n : ℕ, r ^ n • s = 0 := by
  classical
  have h (i : ι) : ∃ n : ℕ, r ^ n • s i = 0 := by
    have hi : f i (s i) = f i 0 := by
      simpa only [DirectSum.lmap_apply, DFinsupp.zero_apply, map_zero] using
        congrArg (fun t ↦ t i) hs
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq r hi
    exact ⟨n, by simpa only [smul_zero] using hn⟩
  choose n hn using h
  refine ⟨s.support.sup n, ?_⟩
  ext i
  change r ^ s.support.sup n • s i = 0
  by_cases hi : i ∈ s.support
  · have hle : n i ≤ s.support.sup n := Finset.le_sup hi
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, mul_smul, smul_comm, hn, smul_zero]
  · rw [DFinsupp.notMem_support_iff.mp hi, smul_zero]

/-- Direct sums preserve localization along powers of a scalar. -/
lemma isLocalizedModule : IsLocalizedModule.Away r (DirectSum.lmap f) :=
  IsLocalizedModule.Away.mk_of_addCommGroup (scalar_isUnit r f)
    (exists_numerator r f) (exists_annihilator r f)

end FLT.Mazur.DirectSumLocalization
