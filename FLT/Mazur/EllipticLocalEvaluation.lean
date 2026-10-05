/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticInfinityEvaluation
public import FLT.Mazur.EllipticFormalCoordinates
public import Mathlib.RingTheory.MvPowerSeries.Evaluation

/-!
# Multivariate convergent evaluation on a complete local chart

A finite family of maximal-ideal parameters defines a convergent ring map.
Every zero-constant series evaluates into the maximal ideal, and the formal
coordinate evaluates to the unique actual infinity-chart coordinate.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K)

/-- Equip the valuation ring with its maximal-ideal topology. -/
local instance localEvaluationWithIdeal : WithIdeal A := ⟨maximalIdeal A⟩

variable [IsAdicComplete (maximalIdeal A) A]

/-- Adic completeness gives completeness of the evaluation topology. -/
local instance localEvaluationCompleteSpace : CompleteSpace A :=
  ((IsAdic.isAdicComplete_iff (R := A) (I := maximalIdeal A) rfl).mp inferInstance).1

/-- Adic separatedness makes the evaluation topology Hausdorff. -/
local instance localEvaluationT2Space : T2Space A :=
  ((IsAdic.isAdicComplete_iff (R := A) (I := maximalIdeal A) rfl).mp inferInstance).2

omit [IsAdicComplete (maximalIdeal A) A] in
/-- Finite families in the maximal ideal admit convergent evaluation. -/
theorem localParameters_hasEval {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ i, a i ∈ maximalIdeal A) : MvPowerSeries.HasEval a where
  hpow i := WithIdeal.isTopologicallyNilpotent_of_mem (ha i)
  tendsto_zero := by simp

/-- Convergent evaluation at a finite family of maximal-ideal parameters. -/
noncomputable def localMvEvaluation {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ i, a i ∈ maximalIdeal A) : MvPowerSeries σ A →+* A :=
  MvPowerSeries.eval₂Hom (φ := RingHom.id A) continuous_id (localParameters_hasEval A a ha)

/-- Multivariate evaluation fixes coefficients. -/
@[simp] theorem localMvEvaluation_C {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ i, a i ∈ maximalIdeal A) (c : A) :
    localMvEvaluation A a ha (MvPowerSeries.C c) = c := by
  simp [localMvEvaluation, MvPowerSeries.coe_eval₂Hom]

/-- Multivariate evaluation sends each variable to its specified parameter. -/
@[simp] theorem localMvEvaluation_X {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ i, a i ∈ maximalIdeal A) (i : σ) :
    localMvEvaluation A a ha (MvPowerSeries.X i) = a i := by
  simp [localMvEvaluation, MvPowerSeries.coe_eval₂Hom]

omit [IsAdicComplete (maximalIdeal A) A] in
/-- Any coefficient-fixing evaluation sends zero-constant series into the maximal ideal. -/
theorem evaluation_mem_maximalIdeal {σ : Type*} (f : MvPowerSeries σ A →+* A)
    (hf : ∀ c, f (MvPowerSeries.C c) = c) {g : MvPowerSeries σ A}
    (hg : g.constantCoeff = 0) : f g ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have hs : IsUnit (1 - MvPowerSeries.C (↑u⁻¹ : A) * g) := by
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    simp [hg]
  have he := (hs.map f).ne_zero
  apply he
  simp only [map_sub, map_one, map_mul, hf, ← hu, Units.inv_mul, sub_self]

/-- Convergent evaluation preserves the maximal-ideal chart. -/
theorem localMvEvaluation_mem {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ i, a i ∈ maximalIdeal A) {g : MvPowerSeries σ A}
    (hg : g.constantCoeff = 0) : localMvEvaluation A a ha g ∈ maximalIdeal A :=
  evaluation_mem_maximalIdeal A _ (localMvEvaluation_C A a ha) hg

/-- Formal coordinate evaluation agrees with the actual convergent chart solution. -/
theorem localMvEvaluation_coordinate {σ : Type*} [Finite σ] (a : σ → A)
    (ha : ∀ i, a i ∈ maximalIdeal A) (W : WeierstrassCurve A)
    {t : MvPowerSeries σ A} (ht : t.constantCoeff = 0) :
    localMvEvaluation A a ha (FormalInfinity.coordinate W t) =
      infinityEvaluation A W (localMvEvaluation A a ha t) (localMvEvaluation_mem A a ha ht) := by
  apply infinityChart_eq_evaluation A W (localMvEvaluation_mem A a ha ht)
    (localMvEvaluation_mem A a ha (FormalInfinity.constantCoeff_coordinate W ht))
  have h := congrArg (localMvEvaluation A a ha) (FormalInfinity.equation_coordinate W ht)
  simpa only [FormalInfinity.Equation, FormalInfinity.curve, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, InfinityChartEquation, map_add, map_mul, map_pow,
    localMvEvaluation_C] using h

end FLT.Mazur
