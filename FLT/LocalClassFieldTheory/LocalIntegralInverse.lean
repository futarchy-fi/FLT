/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AdicSeriesEvaluation
public import FLT.LocalClassFieldTheory.LocalIntegralSeries

/-!
# Evaluated integral exponential and logarithm are inverse

Evaluate the proved formal identities at actual small integers. These are
identities in the complete DVR, not assumptions about a future analytic API.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open PowerSeries IsLocalRing

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L] [CharZero L]
  [IsAdicComplete (maximalIdeal S) S]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

/-- Evaluated scaled exponential after evaluated scaled logarithm returns the input. -/
theorem integralLocalExp_log (x : AdicInteger S L)
    (hx : (dvrPrime S).valuation L (adicIntegerToField S L x) < 1) :
    adicSeriesEval S L (integralExpSeries S L p)
      (adicSeriesEval S L (integralLogSeries S L p) x) = x := by
  rw [← adicSeriesEval_subst _ _ _ _ (integralLogSeries_constantCoeff S L p) _
    (adicInteger_hasEval S L x hx), integralExpSeries_subst_log, adicSeriesEval_X]

/-- Evaluated scaled logarithm after evaluated scaled exponential returns the input. -/
theorem integralLocalLog_exp (x : AdicInteger S L)
    (hx : (dvrPrime S).valuation L (adicIntegerToField S L x) < 1) :
    adicSeriesEval S L (integralLogSeries S L p)
      (adicSeriesEval S L (integralExpSeries S L p) x) = x := by
  rw [← adicSeriesEval_subst _ _ _ _ (integralExpSeries_constantCoeff S L p) _
    (adicInteger_hasEval S L x hx), integralLogSeries_subst_exp, adicSeriesEval_X]

end LocalClassFieldTheory
