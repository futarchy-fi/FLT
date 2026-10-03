/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.LocalScaledCoefficients

/-!
# Inverse exponential and logarithm series over the integer ring

Lift the proved integral coefficients into the DVR. Injectivity of its map
to the fraction field transfers both formal inverse identities back to the
integer ring; no inverse relation is included in the construction's data.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open PowerSeries IsLocalRing

variable (S L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field L] [Algebra S L] [IsFractionRing S L]

/-- Lift an integral-coefficient series from the fraction field to the DVR. -/
def dvrIntegralSeries (f : PowerSeries L)
    (hf : ∀ n, (dvrPrime S).valuation L (coeff n f) ≤ 1) : PowerSeries S :=
  PowerSeries.mk fun n => Classical.choose
    ((dvrAdicValued_integers S L).symm ▸ hf n : coeff n f ∈ Set.range (algebraMap S L))

/-- The lifted series maps to the original series, coefficient by coefficient. -/
theorem dvrIntegralSeries_map (f : PowerSeries L)
    (hf : ∀ n, (dvrPrime S).valuation L (coeff n f) ≤ 1) :
    (dvrIntegralSeries S L f hf).map (algebraMap S L) = f := by
  ext n
  simp only [coeff_map, dvrIntegralSeries, coeff_mk]
  exact Classical.choose_spec
    ((dvrAdicValued_integers S L).symm ▸ hf n : coeff n f ∈ Set.range (algebraMap S L))

variable [CharZero L] (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

/-- The integral series (exp(pX)-1)/p. -/
def integralExpSeries : PowerSeries S :=
  dvrIntegralSeries S L (localScaledSeries (p : L) (exp L - 1))
    (localScaledExp_coeff_integral S L p)

/-- The integral series log(1+pX)/p. -/
def integralLogSeries : PowerSeries S :=
  dvrIntegralSeries S L (localScaledSeries (p : L) (log L))
    (localScaledLog_coeff_integral S L p)

/-- Mapping the integral exponential into the field recovers its explicit formula. -/
theorem integralExpSeries_map :
    (integralExpSeries S L p).map (algebraMap S L) =
      localScaledSeries (p : L) (exp L - 1) := dvrIntegralSeries_map S L _ _

/-- Mapping the integral logarithm into the field recovers its explicit formula. -/
theorem integralLogSeries_map :
    (integralLogSeries S L p).map (algebraMap S L) =
      localScaledSeries (p : L) (log L) := dvrIntegralSeries_map S L _ _

/-- The integral exponential has zero constant term. -/
theorem integralExpSeries_constantCoeff : constantCoeff (integralExpSeries S L p) = 0 := by
  apply (IsFractionRing.injective S L)
  have h := congrArg (coeff 0) (integralExpSeries_map S L p)
  simpa only [coeff_map, coeff_zero_eq_constantCoeff, map_zero,
    localScaledSeries_constantCoeff (p : L) (f := exp L - 1) (by simp)] using h

/-- The integral logarithm has zero constant term. -/
theorem integralLogSeries_constantCoeff : constantCoeff (integralLogSeries S L p) = 0 := by
  apply (IsFractionRing.injective S L)
  have h := congrArg (coeff 0) (integralLogSeries_map S L p)
  simpa only [coeff_map, coeff_zero_eq_constantCoeff, map_zero,
    localScaledSeries_constantCoeff _ constantCoeff_log] using h

/-- The actual integral exponential and logarithm series compose to X. -/
theorem integralExpSeries_subst_log :
    (integralExpSeries S L p).subst (integralLogSeries S L p) = X := by
  apply PowerSeries.map_injective (algebraMap S L) (IsFractionRing.injective S L)
  change MvPowerSeries.map (algebraMap S L) _ = _
  rw [map_subst (HasSubst.of_constantCoeff_zero (integralLogSeries_constantCoeff S L p))]
  change ((integralExpSeries S L p).map (algebraMap S L)).subst
    ((integralLogSeries S L p).map (algebraMap S L)) = _
  rw [
    integralExpSeries_map, integralLogSeries_map, map_X]
  exact localScaledExp_subst_log _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- The reverse integral composition is also X. -/
theorem integralLogSeries_subst_exp :
    (integralLogSeries S L p).subst (integralExpSeries S L p) = X := by
  apply PowerSeries.map_injective (algebraMap S L) (IsFractionRing.injective S L)
  change MvPowerSeries.map (algebraMap S L) _ = _
  rw [map_subst (HasSubst.of_constantCoeff_zero (integralExpSeries_constantCoeff S L p))]
  change ((integralLogSeries S L p).map (algebraMap S L)).subst
    ((integralExpSeries S L p).map (algebraMap S L)) = _
  rw [
    integralLogSeries_map, integralExpSeries_map, map_X]
  exact localScaledLog_subst_exp _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

end LocalClassFieldTheory
