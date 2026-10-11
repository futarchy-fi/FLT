/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonArithmeticNodeNeighborhood
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.Field.Equiv

/-!
# The specified closed node on the original arithmetic charts

Over a field, the two-coordinate ideal is maximal both on the power-series
model and on every original truncated chart. These give actual spectrum points,
and the original coefficient maps carry each stage point to the same node.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [Field K]

/-- The specified coordinate ideal of the complete arithmetic model is maximal. -/
theorem arithmeticNodeIdeal_isMaximal :
    (coordinateIdeal (PowerSeries.X : PowerSeries K)).IsMaximal := by
  let _ : (Ideal.span {PowerSeries.X} : Ideal (PowerSeries K)).IsMaximal := by
    rw [← PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  apply Ideal.Quotient.maximal_of_isField
  exact (coordinateQuotientEquiv (PowerSeries.X : PowerSeries K)).toMulEquiv.isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance)

/-- The node ideal contains the actual stage kernel. -/
theorem arithmeticChartToStage_ker_le_node (m : ℕ) :
    RingHom.ker (arithmeticChartToStage K m) ≤
      coordinateIdeal (PowerSeries.X : PowerSeries K) :=
  (arithmeticChartToStage_ker_le K m).trans (Ideal.pow_le_self (Nat.succ_ne_zero m))

/-- The original stage coordinate ideal is maximal, with no choice of a new point. -/
theorem stageNodeIdeal_isMaximal (m : ℕ) :
    (coordinateIdeal (parameter K m)).IsMaximal := by
  rw [← arithmeticChartToStage_coordinateIdeal K m]
  let _ := arithmeticNodeIdeal_isMaximal K
  exact Ideal.IsMaximal.map_of_surjective_of_ker_le
    (arithmeticChartToStage_surjective K m) (arithmeticChartToStage_ker_le_node K m)

/-- The original complete arithmetic node is the spectrum point defined by (x,y). -/
def arithmeticNodePoint : PrimeSpectrum (ChartRing (PowerSeries.X : PowerSeries K)) :=
  ⟨coordinateIdeal _, (arithmeticNodeIdeal_isMaximal K).isPrime⟩

/-- The original finite-order node is the spectrum point defined by its own coordinates. -/
def stageNodePoint (m : ℕ) : PrimeSpectrum (ChartRing (parameter K m)) :=
  ⟨coordinateIdeal _, (stageNodeIdeal_isMaximal K m).isPrime⟩

/-- Pulling the actual stage node ideal back gives precisely the original arithmetic node ideal. -/
theorem stageNodeIdeal_comap (m : ℕ) :
    (coordinateIdeal (parameter K m)).comap (arithmeticChartToStage K m) =
      coordinateIdeal (PowerSeries.X : PowerSeries K) := by
  rw [← arithmeticChartToStage_coordinateIdeal K m,
    Ideal.comap_map_of_surjective _ (arithmeticChartToStage_surjective K m),
    ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr (arithmeticChartToStage_ker_le_node K m)]

/-- The actual coefficient projection identifies the specified node points. -/
theorem stageNodePoint_comap (m : ℕ) :
    PrimeSpectrum.comap (arithmeticChartToStage K m) (stageNodePoint K m) =
      arithmeticNodePoint K :=
  PrimeSpectrum.ext (stageNodeIdeal_comap K m)

end FLT.Mazur.PolygonInfinitesimalStages
