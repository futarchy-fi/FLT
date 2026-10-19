/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarTestLocalizationKernels
public import Mathlib.Data.Fintype.Order

/-!
# Descent of scalar test equations along finite coefficient covers

Jointly injective coefficient maps detect scalar test kernels. Finiteness
constructs a common exponent before descending the actual power equation;
checking points or reduced coefficient rings would not suffice.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarTestLocalization
variable {R B : Type*} [CommRing R] [CommRing B] (s : R →+* B)

/-- A power equation persists at every larger exponent, with its scalar unchanged. -/
theorem test_power_eq_zero_of_le (b : B) (r : R) {k m : ℕ}
    (hkm : k ≤ m) (hk : b ^ k * s r = 0) : b ^ m * s r = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [pow_add, mul_right_comm, hk, zero_mul]

variable {ι : Type*} [Finite ι] {C : ι → Type*} [∀ i, CommRing (C i)]
  (g : ∀ i, B →+* C i)
  (hg : ∀ x y : B, (∀ i, g i x = g i y) → x = y)
include hg

/-- A finite coefficient cover constructs a uniform exponent for the same scalar equation. -/
theorem exists_uniform_test_power (b : B) (r : R)
    (h : ∀ i, r ∈ testKernel ((g i).comp s) (g i b)) :
    ∃ k : ℕ, b ^ k * s r = 0 := by
  choose k hk using fun i ↦ (mem_testKernel ((g i).comp s) (g i b) r).mp (h i)
  obtain ⟨m, hm⟩ := Finite.exists_le k
  refine ⟨m, hg _ _ ?_⟩
  intro i
  rw [map_mul, map_pow, map_zero]
  exact test_power_eq_zero_of_le ((g i).comp s) (g i b) r (hm i) (hk i)

/-- The entire original kernel, including nilpotent equations, descends from a finite cover. -/
theorem mem_testKernel_iff_cover (b : B) (r : R) :
    r ∈ testKernel s b ↔ ∀ i, r ∈ testKernel ((g i).comp s) (g i b) := by
  constructor
  · intro h i
    obtain ⟨k, hk⟩ := (mem_testKernel s b r).mp h
    apply (mem_testKernel ((g i).comp s) (g i b) r).mpr
    exact ⟨k, by simpa only [map_mul, map_pow, map_zero, RingHom.comp_apply]
      using congrArg (g i) hk⟩
  · intro h
    exact (mem_testKernel s b r).mpr (exists_uniform_test_power s g hg b r h)

/-- Finite refinements compute the original scalar kernel by an exact intersection. -/
theorem testKernel_eq_iInf_cover (b : B) :
    testKernel s b = ⨅ i, testKernel ((g i).comp s) (g i b) := by
  ext r
  rw [Ideal.mem_iInf, mem_testKernel_iff_cover s g hg]

/-- Avoidance of an original scalar prime can be checked independently on every finite branch. -/
theorem testKernel_not_le_iff_cover (b : B) (P : PrimeSpectrum R) :
    ¬ testKernel s b ≤ P.asIdeal ↔
      ∀ i, ¬ testKernel ((g i).comp s) (g i b) ≤ P.asIdeal := by
  let _ := Fintype.ofFinite ι
  rw [testKernel_eq_iInf_cover s g hg, ← Finset.inf_univ_eq_iInf, P.isPrime.inf_le']
  simp only [Finset.mem_univ, true_and, not_exists]

end FLT.Mazur.ScalarTestLocalization
