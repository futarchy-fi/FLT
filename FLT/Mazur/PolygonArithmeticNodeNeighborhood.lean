/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingRingMap
public import FLT.Mazur.PolygonPowerSeriesBase
public import FLT.Mazur.SurjectiveIdealPowerQuotient

/-!
# Original arithmetic node neighborhoods at finite order

The arithmetic xy=q chart maps onto each original truncated chart. Its kernel
is the extended parameter power. Consequently the coordinate-ideal power
neighborhoods agree, through the actual coefficient map, at the same order.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R] (m : ℕ)

/-- The original coefficient map from the arithmetic model to the actual stage chart. -/
def arithmeticChartToStage :
    ChartRing (PowerSeries.X : PowerSeries R) →+* ChartRing (parameter R m) :=
  ringMap (seriesToStage R m).toRingHom _ _ (seriesToStage_X R m)

/-- Every truncated chart section lifts to the original arithmetic chart. -/
theorem arithmeticChartToStage_surjective : Function.Surjective (arithmeticChartToStage R m) :=
  ringMap_surjective _ _ _ _ (seriesToStage_surjective R m)

/-- Coefficient specialization preserves the specified coordinate ideal exactly. -/
theorem arithmeticChartToStage_coordinateIdeal :
    (coordinateIdeal (PowerSeries.X : PowerSeries R)).map (arithmeticChartToStage R m) =
      coordinateIdeal (parameter R m) :=
  ringMap_coordinateIdeal _ _ _ _

/-- The exact chart kernel is the original parameter power extended from the complete base. -/
theorem arithmeticChartToStage_ker :
    RingHom.ker (arithmeticChartToStage R m) =
      (parameterIdeal R).map
        (algebraMap (PowerSeries R) (ChartRing (PowerSeries.X : PowerSeries R))) ^ (m + 1) := by
  rw [arithmeticChartToStage, ringMap_ker _ _ _ _ (seriesToStage_surjective R m),
    seriesToStage_ker, Ideal.map_pow]

/-- The actual chart kernel lies in the matching power of the original node ideal. -/
theorem arithmeticChartToStage_ker_le :
    RingHom.ker (arithmeticChartToStage R m) ≤
      coordinateIdeal (PowerSeries.X : PowerSeries R) ^ (m + 1) := by
  rw [arithmeticChartToStage_ker]
  have hle : (parameterIdeal R).map
      (algebraMap (PowerSeries R) (ChartRing (PowerSeries.X : PowerSeries R))) ≤
        coordinateIdeal (PowerSeries.X : PowerSeries R) := by
    rw [parameterIdeal, Ideal.map_span, Set.image_singleton, Ideal.span_le,
      Set.singleton_subset_iff]
    exact parameter_mem_coordinateIdeal _
  exact pow_le_pow_left' hle _

/-- The original arithmetic and truncated node neighborhoods are canonically identical. -/
def arithmeticNodeNeighborhood :
    (ChartRing (PowerSeries.X : PowerSeries R) ⧸
      coordinateIdeal (PowerSeries.X : PowerSeries R) ^ (m + 1)) ≃+*
        (ChartRing (parameter R m) ⧸ coordinateIdeal (parameter R m) ^ (m + 1)) :=
  (SurjectiveIdealPowerQuotient.equivalence _ (arithmeticChartToStage_surjective R m)
    _ _ (arithmeticChartToStage_ker_le R m)).trans
      (Ideal.quotEquivOfEq (congrArg (fun I ↦ I ^ (m + 1))
        (arithmeticChartToStage_coordinateIdeal R m)))

/-- Neighborhood identification retains the actual map on every chart section. -/
@[simp] theorem arithmeticNodeNeighborhood_mk
    (a : ChartRing (PowerSeries.X : PowerSeries R)) :
    arithmeticNodeNeighborhood R m (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (arithmeticChartToStage R m a) := by
  rw [arithmeticNodeNeighborhood, RingEquiv.trans_apply,
    SurjectiveIdealPowerQuotient.equivalence_mk, Ideal.quotEquivOfEq_mk]

/-- Every original power-series coefficient is retained in the node comparison. -/
theorem arithmeticNodeNeighborhood_scalar (r : PowerSeries R) :
    arithmeticNodeNeighborhood R m
      (Ideal.Quotient.mk _ (algebraMap _ (ChartRing (PowerSeries.X : PowerSeries R)) r)) =
        Ideal.Quotient.mk _
          (algebraMap (Ring R m) (ChartRing (parameter R m)) (seriesToStage R m r)) := by
  rw [arithmeticNodeNeighborhood_mk]
  exact congrArg (Ideal.Quotient.mk _) (ringMap_scalar _ _ _ _ r)

end FLT.Mazur.PolygonInfinitesimalStages
