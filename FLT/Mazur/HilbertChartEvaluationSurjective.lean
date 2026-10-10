/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartBasisAlgebra

/-!
# Surjective polynomial evaluation over a Hilbert chart

After imposing the basis equations, evaluation from the ambient affine space
base changed to the chart is surjective. The original base-ring polynomials
are explicitly mapped to the chart coefficient ring.
-/

@[expose] public noncomputable section

open scoped BigOperators TensorProduct

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)

/-- Cache the coefficient-ring instance for nested tensor inference. -/
local instance evaluationSurjectiveCoefficientsRing :
    CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart-ring instance for nested tensor inference. -/
local instance evaluationSurjectiveChartRing :
    CommRing (ChartRing R I d w) := inferInstance

/-- Polynomial evaluation in the actual chart algebra, with chart-ring coefficients. -/
def chartEvaluation : MvPolynomial I (ChartRing R I d w) →ₐ[ChartRing R I d w]
    ChartAlgebra R I d w :=
  MvPolynomial.aeval fun i ↦ chartInclusion R I d w (generator R I d i)

/-- Extend the coefficients of an ambient polynomial to the actual chart ring. -/
def chartPolynomial : MvPolynomial I R →+* MvPolynomial I (ChartRing R I d w) :=
  MvPolynomial.map ((chartMap R I d w).comp (algebraMap R (Coefficients R I d)))

/-- Polynomial evaluation commutes with this actual scalar extension. -/
theorem chartEvaluation_polynomial (p : MvPolynomial I R) :
    chartEvaluation R I d w (chartPolynomial R I d w p) =
      chartInclusion R I d w (evaluation R I d p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp only [chartPolynomial, MvPolynomial.map_C, RingHom.comp_apply, chartEvaluation,
      MvPolynomial.aeval_C, evaluation]
    rw [IsScalarTower.algebraMap_apply R (Coefficients R I d) (UniversalAlgebra R I d),
      AlgHom.commutes]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul]
    rw [hp]
    congr 1
    simp only [chartPolynomial, MvPolynomial.map_X, chartEvaluation,
      MvPolynomial.aeval_X, evaluation_X]

/-- Every prescribed basis polynomial evaluates to the actual base-changed basis vector. -/
theorem chartEvaluation_basis (i : Fin d) :
    chartEvaluation R I d w (chartPolynomial R I d w (w i)) = chartBasis R I d w i := by
  rw [chartEvaluation_polynomial, chartInclusion_evaluation]

/-- The ambient polynomial map over the chart is surjective. -/
theorem chartEvaluation_surjective : Function.Surjective (chartEvaluation R I d w) := by
  intro a
  refine ⟨∑ i, (chartBasis R I d w).repr a i • chartPolynomial R I d w (w i), ?_⟩
  simp only [map_sum, map_smul, chartEvaluation_basis, Module.Basis.sum_repr]

end FLT.Mazur.HilbertChart
