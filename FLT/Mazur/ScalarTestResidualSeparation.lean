/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarTestKernelProducts

/-!
# One original scalar separating an entire closed residual locus

Exclusion of all higher-test components at every prime of a closed residual
locus is equivalent to a concrete comaximality equation. It constructs one
scalar congruent to one on that locus, annihilating a whole test-ideal power.
This is stronger than vanishing tests only on the exact residual fibers.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ScalarTestLocalization
open ScalarLocalizedIdealNilpotence
variable {R B : Type*} [CommRing R] [CommRing B]
  (s : R →+* B) (a : Finset B) (J : Ideal R)
local notation "I" => Ideal.span (a : Set B)

/-- Coverage of every original residual prime is a finite-kernel comaximality condition. -/
theorem residual_coverage_iff_kernelProduct_sup :
    (∀ P : PrimeSpectrum R, J ≤ P.asIdeal → P ∈ scalarNilpotenceOpen s I) ↔
      kernelProduct s a ⊔ J = ⊤ := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨M, hM, hm⟩ := Ideal.exists_le_maximal (kernelProduct s a ⊔ J) hn
    let P : PrimeSpectrum R := ⟨M, hM.isPrime⟩
    exact (mem_scalarNilpotenceOpen_iff_kernelProduct s a P).mp
      (h P (le_sup_right.trans hm)) (le_sup_left.trans hm)
  · intro h P hp
    apply (mem_scalarNilpotenceOpen_iff_kernelProduct s a P).mpr
    intro hk
    have ht : (⊤ : Ideal R) ≤ P.asIdeal := h ▸ sup_le hk hp
    exact P.isPrime.ne_top (top_le_iff.mp ht)

/-- A finite-kernel certificate constructs an original scalar equal to one on the residual locus. -/
theorem residual_separating_scalar (h : kernelProduct s a ⊔ J = ⊤) :
    ∃ x : R, x ∈ kernelProduct s a ∧ 1 - x ∈ J ∧
      ∃ k : ℕ, s x ∈ (I ^ k).annihilator := by
  obtain ⟨x, hx, y, hy, he⟩ := Submodule.mem_sup.mp
    ((Ideal.eq_top_iff_one _).mp h)
  refine ⟨x, hx, ?_, kernelProduct_power_annihilator s a x hx⟩
  have hyx : y = 1 - x := by linear_combination he
  exact hyx ▸ hy

/-- The residual separating scalar avoids every prime of the full original closed locus. -/
theorem separating_scalar_not_mem (x : R) (hx : 1 - x ∈ J)
    (P : PrimeSpectrum R) (hP : J ≤ P.asIdeal) : x ∉ P.asIdeal := by
  intro hp
  have h1 := P.asIdeal.add_mem (hP hx) hp
  rw [sub_add_cancel] at h1
  exact P.isPrime.one_notMem h1

/-- One constructed original scalar neighborhood handles all residual primes simultaneously. -/
theorem residual_uniform_power_neighborhood
    (h : ∀ P : PrimeSpectrum R, J ≤ P.asIdeal → P ∈ scalarNilpotenceOpen s I) :
    ∃ (x : R) (k : ℕ), 1 - x ∈ J ∧ s x ∈ (I ^ k).annihilator ∧
      (∀ P : PrimeSpectrum R, J ≤ P.asIdeal → x ∉ P.asIdeal) ∧
      ((I).map (algebraMap B (Localization.Away (s x)))) ^ k = ⊥ := by
  obtain ⟨x, _, hx, k, hk⟩ := residual_separating_scalar s a J
    ((residual_coverage_iff_kernelProduct_sup s a J).mp h)
  exact ⟨x, k, hx, hk, separating_scalar_not_mem J x hx,
    FiniteIdealLocalizationDenominators.away_power_eq_bot I k (s x) hk⟩

/-- Nilpotent residual ideals allow the separating scalar to be removed entirely. -/
theorem nilpotent_of_residual_coverage (hJ : IsNilpotent J)
    (h : ∀ P : PrimeSpectrum R, J ≤ P.asIdeal → P ∈ scalarNilpotenceOpen s I) :
    IsNilpotent I := by
  apply (scalarNilpotenceOpen_eq_top_iff s I (Submodule.fg_span a.finite_toSet)).mp
  apply top_unique
  intro P _
  apply h P
  obtain ⟨k, hk⟩ := hJ
  apply Ideal.IsPrime.le_of_pow_le (n := k)
  exact hk ▸ bot_le

end FLT.Mazur.ScalarTestLocalization
