/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ValuationRingModel
public import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# Completeness of the realized valuation ring

The canonical image of the complete extension DVR is complete for its own
maximal ideal. Thus the actual formal-parameter evaluation theorems apply
to the same valuation subring used for the good and multiplicative comparisons.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing

variable (R K : Type*) [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Realization in the fraction field preserves completeness for the maximal ideal. -/
theorem fractionValuationSubring_isAdicComplete [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal (fractionValuationSubring R K))
      (fractionValuationSubring R K) := by
  rw [← map_ringEquiv_maximalIdeal (fractionValuationEquiv R K)]
  exact (IsAdicComplete.congr_ringEquiv _ _).mpr inferInstance

end FLT.Mazur
