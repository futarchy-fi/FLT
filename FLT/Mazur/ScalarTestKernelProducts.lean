/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarTestLocalizationKernels

/-!
# A finite scalar obstruction ideal and exact common denominators

The product of the principal-test kernels defines the entire closed scalar
obstruction. Every element of this product, without raising that scalar to
a power, kills a whole power of the finite test ideal. Independent equations
on the charts multiply to an explicit common scalar equation.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarTestLocalization
open ScalarLocalizedIdealNilpotence
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (a : Finset B)
local notation "I" => Ideal.span (a : Set B)

/-- The finite product of the original scalar kernels on the test charts. -/
def kernelProduct : Ideal R := ∏ b ∈ a, testKernel s b

/-- The finite product defines exactly the scalar obstruction, including all generizing centers. -/
theorem mem_scalarNilpotenceOpen_iff_kernelProduct (P : PrimeSpectrum R) :
    P ∈ scalarNilpotenceOpen s I ↔ ¬ kernelProduct s a ≤ P.asIdeal := by
  rw [mem_scalarNilpotenceOpen_iff_kernels, kernelProduct, P.isPrime.prod_le]
  push Not
  rfl

/-- The complement is one closed set defined by a constructed ideal of the original scalars. -/
theorem scalarNilpotenceOpen_compl_kernelProduct :
    (scalarNilpotenceOpen s I : Set (PrimeSpectrum R))ᶜ =
      PrimeSpectrum.zeroLocus (kernelProduct s a : Set R) := by
  ext P
  simpa only [Set.mem_compl_iff, SetLike.mem_coe, PrimeSpectrum.mem_zeroLocus,
    SetLike.coe_subset_coe, not_not] using
    not_congr (mem_scalarNilpotenceOpen_iff_kernelProduct s a P)

/-- Simultaneous chart equations give a whole-power equation for the very same scalar. -/
theorem exists_power_annihilator_iff_kernels (r : R) :
    (∃ k : ℕ, s r ∈ (I ^ k).annihilator) ↔ ∀ b ∈ a, r ∈ testKernel s b := by
  refine ⟨fun ⟨k, hk⟩ ↦ scalar_annihilator_mem_kernels s a k r hk, ?_⟩
  intro h
  let J : Ideal B := (Ideal.span ({s r} : Set B)).annihilator
  have hIJ : I ≤ J.radical := by
    apply Ideal.span_le.mpr
    intro b hb
    obtain ⟨k, hk⟩ := (mem_testKernel s b r).mp (h b hb)
    exact ⟨k, (Submodule.mem_annihilator_span_singleton (s r) (b ^ k)).mpr hk⟩
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ
    (Submodule.fg_span a.finite_toSet)
  refine ⟨k, Submodule.mem_annihilator.mpr ?_⟩
  intro b hb
  have he := (Submodule.mem_annihilator_span_singleton (s r) b).mp (hk hb)
  simpa only [smul_eq_mul, mul_comm] using he

/-- Every element of the finite product kills a whole test power without changing that scalar. -/
theorem kernelProduct_power_annihilator (r : R) (hr : r ∈ kernelProduct s a) :
    ∃ k : ℕ, s r ∈ (I ^ k).annihilator := by
  apply (exists_power_annihilator_iff_kernels s a r).mpr
  intro b hb
  exact (Ideal.prod_le_inf.trans (Finset.inf_le hb)) hr

/-- Independent equations on all charts multiply to an explicit common original scalar. -/
theorem product_of_chart_equations (P : PrimeSpectrum R) (r : B → R)
    (hr : ∀ b ∈ a, r b ∉ P.asIdeal)
    (he : ∀ b ∈ a, r b ∈ testKernel s b) :
    (∏ b ∈ a, r b) ∉ P.asIdeal ∧
      ∃ k : ℕ, s (∏ b ∈ a, r b) ∈ (I ^ k).annihilator := by
  refine ⟨?_, kernelProduct_power_annihilator s a _ (Ideal.prod_mem_prod he)⟩
  intro hp
  obtain ⟨b, hb, hm⟩ := Ideal.IsPrime.prod_mem_iff.mp hp
  exact hr b hb hm

/-- A chosen finite family of scalar chart equations gives a full nilpotent neighborhood. -/
theorem product_chart_equations_neighborhood (P : PrimeSpectrum R) (r : B → R)
    (hr : ∀ b ∈ a, r b ∉ P.asIdeal)
    (he : ∀ b ∈ a, r b ∈ testKernel s b) :
    ∃ k : ℕ, (∏ b ∈ a, r b) ∉ P.asIdeal ∧
      ((I).map (algebraMap B (Localization.Away (s (∏ b ∈ a, r b))))) ^ k = ⊥ := by
  obtain ⟨hp, k, hk⟩ := product_of_chart_equations s a P r hr he
  exact ⟨k, hp, FiniteIdealLocalizationDenominators.away_power_eq_bot I k _ hk⟩

end FLT.Mazur.ScalarTestLocalization
