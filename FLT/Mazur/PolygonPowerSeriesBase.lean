/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerSeriesNilpotentHom
public import FLT.Mazur.PolygonInfinitesimalStageReduction
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.PowerSeries.Ideal

/-!
# A complete coefficient base for the actual infinitesimal polygons

The power-series ring has the existing stage rings as its parameter-adic
quotients. Its quotient maps preserve the chosen parameters and commute with
the actual successive restrictions and closed-fiber reductions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.PolygonInfinitesimalStages

variable (R : Type*) [CommRing R] (m : ℕ)

/-- The ideal of definition on the complete power-series coefficient base. -/
def parameterIdeal : Ideal (PowerSeries R) := Ideal.span {PowerSeries.X}

/-- Power series are complete for the actual ideal of definition. -/
instance parameterIdeal_complete :
    IsAdicComplete (parameterIdeal R) (PowerSeries R) :=
  inferInstanceAs (IsAdicComplete (Ideal.span {PowerSeries.X}) (PowerSeries R))

/-- The canonical map from the complete coefficient base to the actual stage ring. -/
def seriesToStage : PowerSeries R →ₐ[R] Ring R m :=
  PowerSeriesTruncatedPolynomial.toStage R m

/-- The actual smoothing parameter is the image of the power-series parameter. -/
@[simp] theorem seriesToStage_X :
    seriesToStage R m PowerSeries.X = parameter R m :=
  PowerSeriesTruncatedPolynomial.toStage_X R m

/-- Every actual stage coefficient lifts to the complete base. -/
theorem seriesToStage_surjective : Function.Surjective (seriesToStage R m) :=
  PowerSeriesTruncatedPolynomial.toStage_surjective R m

/-- The stage map kills exactly the prescribed power of the ideal of definition. -/
theorem seriesToStage_ker :
    RingHom.ker (seriesToStage R m).toRingHom = parameterIdeal R ^ (m + 1) := by
  rw [parameterIdeal, Ideal.span_singleton_pow]
  exact PowerSeriesTruncatedPolynomial.ker_toStage R m

/-- The complete-base quotient is the original truncated polynomial coefficient algebra. -/
def seriesQuotientEquiv :
    (PowerSeries R ⧸ parameterIdeal R ^ (m + 1)) ≃ₐ[R] Ring R m :=
  (Ideal.quotientEquivAlgOfEq R (seriesToStage_ker R m).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (seriesToStage_surjective R m))

/-- The quotient comparison retains the specified quotient map, not just the ring type. -/
@[simp] theorem seriesQuotientEquiv_mk (f : PowerSeries R) :
    seriesQuotientEquiv R m (Ideal.Quotient.mk _ f) = seriesToStage R m f := by
  rw [seriesQuotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- Successive restrictions commute with the maps from the complete base. -/
theorem restriction_seriesToStage :
    (restriction R m).comp (seriesToStage R (m + 1)) = seriesToStage R m := by
  apply PowerSeriesNilpotentHom.ext
  · simpa only [AlgHom.comp_apply, seriesToStage_X, restriction_parameter] using
      (parameter_nilpotent R m).out
  · simp

/-- The original closed-fiber reduction is the constant coefficient of the power series. -/
theorem reduction_seriesToStage (f : PowerSeries R) :
    reduction R m (seriesToStage R m f) = PowerSeries.constantCoeff f := by
  change reduction R m (AdjoinRoot.mk _ (PowerSeries.trunc (m + 1) f)) = _
  rw [reduction_mk, PowerSeries.coeff_trunc, ite_eq_left (Nat.zero_lt_succ m)]
  exact PowerSeries.coeff_zero_eq_constantCoeff_apply f

end FLT.Mazur.PolygonInfinitesimalStages
