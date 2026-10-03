/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.LocalIntegralInverse
public import FLT.LocalClassFieldTheory.LocalSeriesComparison

/-!
# Inverse identities for the actual local exponential and logarithm

Every x with v(x) < v(p) is p times a topologically nilpotent integer.
The evaluated integral inverse identities therefore give both analytic
composition identities on this explicit neighborhood.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing PowerSeries

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L] [CharZero L]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

omit [CharP (ResidueField S) p] in
/-- A point of the convergence ball is p times a strictly small integral element. -/
theorem localSeries_exists_coordinate (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    ∃ t : AdicInteger S L, x = (p : L) * adicIntegerToField S L t ∧
      (dvrPrime S).valuation L (adicIntegerToField S L t) < 1 := by
  have ht : (dvrPrime S).valuation L (x / (p : L)) < 1 := by
    rwa [map_div₀, div_lt_one₀ (localExpRadius_pos S L p)]
  have hmem : x / (p : L) ∈ Set.range (algebraMap S L) :=
    (dvrAdicValued_integers S L).symm ▸ ht.le
  obtain ⟨s, hs⟩ := hmem
  refine ⟨(adicIntegerEquiv S L).symm s, ?_, ?_⟩
  · change x = (p : L) * algebraMap S L s
    rw [hs, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]
  · change (dvrPrime S).valuation L (algebraMap S L s) < 1
    rwa [hs]

variable [IsAdicComplete (maximalIdeal S) S]

/-- The exponential displacement has valuation at most that of its input. -/
theorem adicLocalExp_sub_one_le (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    (dvrPrime S).valuation L (adicLocalExp S L x - 1) ≤ (dvrPrime S).valuation L x := by
  obtain ⟨t, rfl, ht⟩ := localSeries_exists_coordinate S L p x hx
  rw [adicLocalExp_eq_integral S L p t ht, add_sub_cancel_left, map_mul, map_mul]
  exact mul_le_mul' le_rfl (adicSeriesEval_field_le S L _
    (integralExpSeries_constantCoeff S L p) t ht)

/-- The logarithm has valuation at most that of the principal-unit displacement. -/
theorem adicLocalLog_le (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    (dvrPrime S).valuation L (adicLocalLog S L (1 + x)) ≤ (dvrPrime S).valuation L x := by
  obtain ⟨t, rfl, ht⟩ := localSeries_exists_coordinate S L p x hx
  rw [adicLocalLog_eq_integral S L p t ht, map_mul, map_mul]
  exact mul_le_mul' le_rfl (adicSeriesEval_field_le S L _
    (integralLogSeries_constantCoeff S L p) t ht)

/-- The local logarithm is a left inverse of the actual exponential sum. -/
theorem adicLocalLog_exp (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    adicLocalLog S L (adicLocalExp S L x) = x := by
  obtain ⟨t, rfl, ht⟩ := localSeries_exists_coordinate S L p x hx
  have he := (adicSeriesEval_field_le S L _
    (integralExpSeries_constantCoeff S L p) t ht).trans_lt ht
  rw [adicLocalExp_eq_integral S L p t ht, adicLocalLog_eq_integral S L p _ he,
    integralLocalLog_exp S L p t ht]

/-- The actual exponential sum is a left inverse of logarithm near one. -/
theorem adicLocalExp_log (x : L)
    (hx : (dvrPrime S).valuation L x < (dvrPrime S).valuation L (p : L)) :
    adicLocalExp S L (adicLocalLog S L (1 + x)) = 1 + x := by
  obtain ⟨t, rfl, ht⟩ := localSeries_exists_coordinate S L p x hx
  have hl := (adicSeriesEval_field_le S L _
    (integralLogSeries_constantCoeff S L p) t ht).trans_lt ht
  rw [adicLocalLog_eq_integral S L p t ht, adicLocalExp_eq_integral S L p _ hl,
    integralLocalExp_log S L p t ht]

end LocalClassFieldTheory
