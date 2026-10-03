/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.NormalLatticeDenominators

/-!
# A maximal-ideal power inside the normal lattice

A common denominator gives a nonzero principal ideal of the larger ring
inside the lattice. In a DVR that ideal is a maximal-ideal power.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open scoped nonZeroDivisors

variable (R S K L : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The constructed lattice contains an actual sufficiently high maximal-ideal power. -/
theorem integralNormalLattice_contains_maximalIdeal_power :
    ∃ n : ℕ, ∀ x : S, x ∈ IsLocalRing.maximalIdeal S ^ n →
      algebraMap S L x ∈ integralNormalLattice R K L := by
  obtain ⟨d, hd, hdx⟩ := integralNormalLattice_common_denominator R S K L
  have hdS : algebraMap R S d ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective R S).ne hd
  have hI : (Ideal.span {algebraMap R S d} : Ideal S) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hdS
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    hI hπ
  refine ⟨n, fun x hx => ?_⟩
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hn,
    Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, ← IsScalarTower.algebraMap_apply R S L, ← Algebra.smul_def]
  exact hdx y

end LocalClassFieldTheory
