/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.AdicSeriesEvaluation
public import FLT.LocalClassFieldTheory.ValuationUniformSeries

/-!
# Field values of integral series

Evaluation in the complete DVR maps to the expected convergent sum in
its fraction field. A zero-constant integral series sends each small
valuation ball into itself.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open PowerSeries IsLocalRing IsDedekindDomain

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- Every element of the topological integer copy is integral in the field. -/
theorem adicIntegerToField_le_one (x : AdicInteger S L) :
    (dvrPrime S).valuation L (adicIntegerToField S L x) ≤ 1 :=
  HeightOneSpectrum.valuation_le_one (dvrPrime S) (adicIntegerEquiv S L x)

omit [IsDomain S] [IsDiscreteValuationRing S] [IsFractionRing S L] in
/-- Inclusion of a scalar integer agrees with the original algebra map. -/
theorem adicIntegerToField_algebraMap (s : S) :
    adicIntegerToField S L (algebraMap S (AdicInteger S L) s) = algebraMap S L s := rfl

variable [IsAdicComplete (maximalIdeal S) S]

/-- The integer-ring evaluation gives the monomial sum in the fraction field. -/
theorem adicSeriesEval_field_hasSum (f : PowerSeries S) (x : AdicInteger S L)
    (hx : (dvrPrime S).valuation L (adicIntegerToField S L x) < 1) :
    letI := dvrAdicValued S L
    HasSum (fun n => algebraMap S L (coeff n f) * adicIntegerToField S L x ^ n)
      (adicIntegerToField S L (adicSeriesEval S L f x)) := by
  let := dvrAdicValued S L
  have h := (adicSeriesEval_hasSum S L f x (adicInteger_hasEval S L x hx)).map
    (adicIntegerToField S L).toAddMonoidHom
    (adicIntegerToField_isUniformInducing S L).uniformContinuous.continuous
  change HasSum (fun n => adicIntegerToField S L
    (algebraMap S (AdicInteger S L) (coeff n f) * x ^ n))
    (adicIntegerToField S L (adicSeriesEval S L f x)) at h
  simpa only [map_mul, map_pow,
    adicIntegerToField_algebraMap] using h

/-- A zero-constant integral series preserves every strictly small valuation ball. -/
theorem adicSeriesEval_field_le (f : PowerSeries S) (hf : constantCoeff f = 0)
    (x : AdicInteger S L)
    (hx : (dvrPrime S).valuation L (adicIntegerToField S L x) < 1) :
    (dvrPrime S).valuation L (adicIntegerToField S L (adicSeriesEval S L f x)) ≤
      (dvrPrime S).valuation L (adicIntegerToField S L x) := by
  let := dvrAdicValued S L
  have h := adicSeriesEval_field_hasSum S L f x hx
  rw [← h.tsum_eq]
  apply valuation_tsum_le h.summable
  intro n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff, hf]
  | succ n =>
    change (dvrPrime S).valuation L _ ≤ (dvrPrime S).valuation L _
    rw [map_mul, map_pow]
    calc
      _ ≤ 1 * (dvrPrime S).valuation L (adicIntegerToField S L x) ^ (n + 1) :=
        mul_le_mul' (HeightOneSpectrum.valuation_le_one (dvrPrime S) _) le_rfl
      _ ≤ (dvrPrime S).valuation L (adicIntegerToField S L x) := by
        simpa using pow_le_pow_right_of_le_one' hx.le (Nat.le_add_left 1 n)

end LocalClassFieldTheory
