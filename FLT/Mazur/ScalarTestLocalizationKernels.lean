/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarIdealNilpotenceOpen

/-!
# Scalar kernels of finitely many principal tests

The kernel on each full principal test chart consists of original scalars
annihilated by a power of that test. Avoiding a scalar prime in every such
kernel is equivalent to killing a whole power of the finite test ideal by
one scalar outside that prime. No reduction or Noetherian hypothesis is used.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarTestLocalization
open ScalarLocalizedIdealNilpotence
variable {R B : Type*} [CommRing R] [CommRing B] (s : R →+* B)

/-- Original scalar equations on the full principal chart of a test. -/
def testKernel (b : B) : Ideal R :=
  RingHom.ker ((algebraMap B (Localization.Away b)).comp s)

/-- A kernel equation means actual power annihilation before localization. -/
theorem mem_testKernel (b : B) (r : R) :
    r ∈ testKernel s b ↔ ∃ k : ℕ, b ^ k * s r = 0 := by
  change algebraMap B (Localization.Away b) (s r) = 0 ↔ _
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers b)]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨k, hk⟩ := u.property
    exact ⟨k, by simpa only [hk] using hu⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨b ^ k, ⟨k, rfl⟩⟩, hk⟩

/-- A scalar test equation excludes a prime precisely when that test is forced to vanish. -/
theorem test_mem_prime_of_kernel {b : B} {r : R} (hr : r ∈ testKernel s b)
    (Q : PrimeSpectrum B) (hq : s r ∉ Q.asIdeal) : b ∈ Q.asIdeal := by
  obtain ⟨k, hk⟩ := (mem_testKernel s b r).mp hr
  have hm : b ^ k * s r ∈ Q.asIdeal := hk ▸ Q.asIdeal.zero_mem
  exact Q.isPrime.mem_of_pow_mem k ((Q.isPrime.mem_or_mem hm).resolve_right hq)

variable (a : Finset B)
local notation "I" => Ideal.span (a : Set B)

/-- Each finite original chart kernel must avoid the unchanged scalar prime. -/
theorem mem_scalarNilpotenceOpen_iff_kernels (P : PrimeSpectrum R) :
    P ∈ scalarNilpotenceOpen s I ↔ ∀ b ∈ a, ¬ testKernel s b ≤ P.asIdeal := by
  constructor
  · intro h b hb hle
    obtain ⟨k, r, hr, ha⟩ := (mem_scalarNilpotenceOpen s I P).mp h
    apply hr
    apply hle
    apply (mem_testKernel s b r).mpr
    refine ⟨k, ?_⟩
    have hpow : b ^ k ∈ I ^ k := Ideal.pow_mem_pow (Ideal.subset_span hb) k
    simpa only [smul_eq_mul, mul_comm] using
      Submodule.mem_annihilator.mp ha (b ^ k) hpow
  · intro h
    rw [mem_scalarNilpotenceOpen_iff_localized s I (Submodule.fg_span a.finite_toSet)]
    apply (nilpotent_iff_primes s I P.asIdeal (Submodule.fg_span a.finite_toSet)).mpr
    intro Q hQ
    apply Ideal.span_le.mpr
    intro b hb
    obtain ⟨r, hr, hp⟩ := IsConcreteLE.not_le_iff_exists.mp (h b hb)
    exact test_mem_prime_of_kernel s hr Q (fun hq ↦ hp (hQ hq))

/-- Independently found chart equations construct one scalar killing the entire test ideal power. -/
theorem power_annihilator_of_kernels (P : PrimeSpectrum R)
    (h : ∀ b ∈ a, ∃ r : R, r ∉ P.asIdeal ∧ r ∈ testKernel s b) :
    ∃ (k : ℕ) (r : R), r ∉ P.asIdeal ∧ s r ∈ (I ^ k).annihilator := by
  apply (mem_scalarNilpotenceOpen s I P).mp
  apply (mem_scalarNilpotenceOpen_iff_kernels s a P).mpr
  intro b hb hle
  obtain ⟨r, hr, he⟩ := h b hb
  exact hr (hle he)

/-- One whole-power certificate gives the same scalar equation on every full test chart. -/
theorem scalar_annihilator_mem_kernels (k : ℕ) (r : R)
    (hr : s r ∈ (I ^ k).annihilator) : ∀ b ∈ a, r ∈ testKernel s b := by
  intro b hb
  apply (mem_testKernel s b r).mpr
  refine ⟨k, ?_⟩
  simpa only [smul_eq_mul, mul_comm] using
    Submodule.mem_annihilator.mp hr (b ^ k) (Ideal.pow_mem_pow (Ideal.subset_span hb) k)

end FLT.Mazur.ScalarTestLocalization
