/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonArithmeticNodePoint
public import FLT.Mazur.PolygonInfinitesimalChartRestriction

/-!
# Original transitions on arithmetic node neighborhoods

The neighborhood comparisons commute with the original adjacent chart maps.
Their specified closed points are retained by these same maps, which are the
restrictions of the actual glued family transitions.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R] (m : ℕ)

/-- Original adjacent chart restriction commutes with the complete coefficient map. -/
theorem stageChartRestriction_arithmeticChartToStage
    (a : ChartRing (PowerSeries.X : PowerSeries R)) :
    stageChartRestriction R m (arithmeticChartToStage R (m + 1) a) =
      arithmeticChartToStage R m a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [stageChartRestriction, arithmeticChartToStage, ringMap_mk,
    MvPolynomial.map_map]
  exact congrArg (fun f : PowerSeries R →ₐ[R] Ring R m ↦
    Ideal.Quotient.mk (relationIdeal (parameter R m)) (MvPolynomial.map f.toRingHom p))
      (restriction_seriesToStage R m)

/-- The actual adjacent chart map descends to its matching node neighborhoods. -/
def arithmeticNodeTransition :
    (ChartRing (parameter R (m + 1)) ⧸ coordinateIdeal (parameter R (m + 1)) ^ (m + 2)) →+*
      (ChartRing (parameter R m) ⧸ coordinateIdeal (parameter R m) ^ (m + 1)) :=
  Ideal.quotientMap _ (stageChartRestriction R m) (by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow, stageChartRestriction_coordinateIdeal]
    exact Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))

/-- The neighborhood transition keeps the original restriction on every representative. -/
@[simp] theorem arithmeticNodeTransition_mk (a : ChartRing (parameter R (m + 1))) :
    arithmeticNodeTransition R m (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (stageChartRestriction R m a) := rfl

/-- The arithmetic node comparisons commute with the original adjacent transitions. -/
theorem arithmeticNodeNeighborhood_transition
    (a : ChartRing (PowerSeries.X : PowerSeries R) ⧸
      coordinateIdeal (PowerSeries.X : PowerSeries R) ^ (m + 2)) :
    arithmeticNodeTransition R m (arithmeticNodeNeighborhood R (m + 1) a) =
      arithmeticNodeNeighborhood R m
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))) a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [arithmeticNodeNeighborhood_mk, arithmeticNodeTransition_mk,
    stageChartRestriction_arithmeticChartToStage, Ideal.Quotient.factor_mk,
    arithmeticNodeNeighborhood_mk]

/-- The matching original node-neighborhood transition is surjective. -/
theorem arithmeticNodeTransition_surjective :
    Function.Surjective (arithmeticNodeTransition R m) := by
  intro a
  obtain ⟨a, rfl⟩ := (arithmeticNodeNeighborhood R m).surjective a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨arithmeticNodeNeighborhood R (m + 1) (Ideal.Quotient.mk _ a), ?_⟩
  rw [arithmeticNodeNeighborhood_transition, Ideal.Quotient.factor_mk]

variable (K : Type*) [Field K]

/-- The actual adjacent chart restriction retains precisely the chosen closed node ideal. -/
theorem stageChartRestriction_nodeIdeal :
    (coordinateIdeal (parameter K m)).comap (stageChartRestriction K m) =
      coordinateIdeal (parameter K (m + 1)) := by
  let _ := stageNodeIdeal_isMaximal K (m + 1)
  rw [← stageChartRestriction_coordinateIdeal K m]
  apply Ideal.comap_map_eq_self_of_isMaximal
  rw [stageChartRestriction_coordinateIdeal]
  exact (stageNodeIdeal_isMaximal K m).ne_top

/-- The specified stage node points commute with the original adjacent chart restriction. -/
theorem stageChartRestriction_nodePoint :
    PrimeSpectrum.comap (stageChartRestriction K m) (stageNodePoint K m) =
      stageNodePoint K (m + 1) :=
  PrimeSpectrum.ext (stageChartRestriction_nodeIdeal m K)

end FLT.Mazur.PolygonInfinitesimalStages
