/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.DedekindDomain.AdicValuation

/-!
# Ideal exponents under completion

Extending an ideal of a Dedekind domain to the integers of a completion
preserves its exponent at the chosen prime. This applies to the global
different without identifying its extension with the local different.
-/

@[expose] public noncomputable section

open UniqueFactorizationMonoid

namespace IsDedekindDomain.HeightOneSpectrum

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [IsDedekindDomain A] (v : HeightOneSpectrum A)

/-- Pulling back a power of the completed maximal ideal gives the same power
of the original prime. -/
theorem comap_completionIdeal_pow (n : ℕ) :
    Ideal.comap (algebraMap A (v.adicCompletionIntegers K))
      (v.completionIdeal K ^ n) = v.asIdeal ^ n := by
  ext x
  rw [Ideal.mem_comap, adicCompletion.mem_completionIdeal_pow,
    algebraMap_completionIntegers, valuedAdicCompletion_eq_valuation,
    valuation_of_algebraMap]
  exact v.intValuation_le_pow_iff_mem x n

/-- Completion preserves containment in each power of the chosen prime. -/
theorem map_le_completionIdeal_pow_iff (I : Ideal A) (n : ℕ) :
    I.map (algebraMap A (v.adicCompletionIntegers K)) ≤ v.completionIdeal K ^ n ↔
      I ≤ v.asIdeal ^ n := by
  rw [Ideal.map_le_iff_le_comap, comap_completionIdeal_pow]

/-- The exponent of the completed maximal ideal in an extended ideal is the
exponent of the original prime, including the convention at the zero ideal. -/
theorem count_normalizedFactors_map_completion (I : Ideal A) :
    (normalizedFactors (I.map (algebraMap A (v.adicCompletionIntegers K)))).count
      (v.completionIdeal K) = (normalizedFactors I).count v.asIdeal := by
  classical
  by_cases hI : I = ⊥
  · subst I
    rw [Ideal.map_bot]
    change (normalizedFactors (0 : Ideal (v.adicCompletionIntegers K))).count _ =
      (normalizedFactors (0 : Ideal A)).count _
    simp only [normalizedFactors_zero, Multiset.count_zero]
  have hd (n : ℕ) : I ≤ v.asIdeal ^ n ↔ n ≤ (normalizedFactors I).count v.asIdeal := by
    rw [← Ideal.dvd_iff_le, pow_dvd_iff_le_emultiplicity,
      emultiplicity_eq_count_normalizedFactors v.irreducible hI, normalize_eq,
      ENat.natCast_le_natCast]
  apply Ideal.count_normalizedFactors_eq
  · exact (map_le_completionIdeal_pow_iff K v I _).mpr ((hd _).mpr le_rfl)
  · rw [map_le_completionIdeal_pow_iff, hd]
    exact Nat.not_succ_le_self _

end IsDedekindDomain.HeightOneSpectrum
