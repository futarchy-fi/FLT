/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticInfinityParameter
public import FLT.Mazur.EllipticInfinityPowerSeries
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.PowerSeries.Evaluation

/-!
# Convergent evaluation of the infinity coordinate

On a valuation ring complete for its maximal-ideal topology, the integral
infinity series converges at every maximal-ideal parameter. Its value is the
unique maximal-ideal chart coordinate. In particular it recovers the actual
projective representative of each point of E₁.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing WeierstrassCurve.Projective

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Use the maximal-ideal topology for convergent infinity evaluation. -/
local instance infinityEvaluationWithIdeal : WithIdeal A := ⟨maximalIdeal A⟩

variable [IsAdicComplete (maximalIdeal A) A]

/-- Adic completeness supplies completeness for the evaluation topology. -/
local instance infinityEvaluationCompleteSpace : CompleteSpace A :=
  ((IsAdic.isAdicComplete_iff (R := A) (I := maximalIdeal A) rfl).mp inferInstance).1

/-- Adic separatedness supplies the Hausdorff evaluation topology. -/
local instance infinityEvaluationT2Space : T2Space A :=
  ((IsAdic.isAdicComplete_iff (R := A) (I := maximalIdeal A) rfl).mp inferInstance).2

/-- Convergent power-series evaluation at a maximal-ideal parameter. -/
noncomputable def localSeriesEvaluation (t : A) (ht : t ∈ maximalIdeal A) : PowerSeries A →+* A :=
  PowerSeries.eval₂Hom (φ := RingHom.id A) continuous_id
    (WithIdeal.isTopologicallyNilpotent_of_mem ht)

/-- Convergent evaluation sends a coefficient to itself. -/
@[simp] theorem localSeriesEvaluation_C (t : A) (ht : t ∈ maximalIdeal A) (a : A) :
    localSeriesEvaluation A t ht (PowerSeries.C a) = a := by
  simp [localSeriesEvaluation, PowerSeries.coe_eval₂Hom]

/-- Convergent evaluation sends the formal parameter to the specified element. -/
@[simp] theorem localSeriesEvaluation_X (t : A) (ht : t ∈ maximalIdeal A) :
    localSeriesEvaluation A t ht PowerSeries.X = t := by
  simp [localSeriesEvaluation, PowerSeries.coe_eval₂Hom]

/-- The convergent infinity coordinate. -/
noncomputable def infinityEvaluation (t : A) (ht : t ∈ maximalIdeal A) : A :=
  localSeriesEvaluation A t ht (infinitySeries W)

/-- The evaluated coordinate satisfies the actual Weierstrass chart equation. -/
theorem infinityEvaluation_equation (t : A) (ht : t ∈ maximalIdeal A) :
    InfinityChartEquation A W t (infinityEvaluation A W t ht) := by
  have h := congrArg (localSeriesEvaluation A t ht) (infinitySeries_equation W)
  simpa only [InfinitySeriesEquation, map_add, map_mul, map_pow,
    localSeriesEvaluation_C, localSeriesEvaluation_X, InfinityChartEquation,
    infinityEvaluation] using h

/-- The evaluated coordinate stays in the maximal ideal. -/
theorem infinityEvaluation_mem (t : A) (ht : t ∈ maximalIdeal A) :
    infinityEvaluation A W t ht ∈ maximalIdeal A := by
  obtain ⟨u, hu⟩ := X_cube_dvd_infinitySeries W
  unfold infinityEvaluation
  rw [hu, map_mul, map_pow, localSeriesEvaluation_X]
  exact (maximalIdeal A).mul_mem_right _ ((maximalIdeal A).pow_mem_of_mem ht 3 (by decide))

/-- Every actual maximal-ideal chart coordinate equals convergent evaluation. -/
theorem infinityChart_eq_evaluation {t s : A} (ht : t ∈ maximalIdeal A)
    (hs : s ∈ maximalIdeal A) (he : InfinityChartEquation A W t s) :
    s = infinityEvaluation A W t ht :=
  infinityChart_unique A W ht hs (infinityEvaluation_mem A W t ht) he
    (infinityEvaluation_equation A W t ht)

/-- Convergent evaluation reconstructs every actual E₁ point from its parameter. -/
theorem ellipticE1_point_eq_evaluation (P : ellipticE1 A W) :
    P.val.point = ⟦![(infinityParameter A W P : K), -1,
      (infinityEvaluation A W (infinityParameter A W P) (infinityParameter_mem A W P) : K)]⟧ := by
  obtain ⟨s, ht, hs, he, hp⟩ := (exists_ellipticE1_chart A W P).choose_spec
  change InfinityChartEquation A W (infinityParameter A W P) s at he
  have h := infinityChart_eq_evaluation A W (infinityParameter_mem A W P) hs he
  change P.val.point = ⟦![(infinityParameter A W P : K), -1, (s : K)]⟧ at hp
  simpa only [h] using hp

end FLT.Mazur
