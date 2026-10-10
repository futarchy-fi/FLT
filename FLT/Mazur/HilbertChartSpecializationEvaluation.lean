/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartSpecialization
public import FLT.Mazur.HilbertChartEvaluationSurjective

/-!
# Ambient compatibility of chart reconstruction

Reconstruction respects every ambient polynomial, over both the original base
and the test ring. Thus it identifies actual quotient maps, not merely algebras.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable {S A : Type*} [CommRing S] [CommRing A] [Algebra R S] [Algebra S A]
variable [Algebra R A] [IsScalarTower R S A]
variable (v : Module.Basis (Fin d) S A) (x : I → A)
variable (w : Fin d → MvPolynomial I R)
variable (hw : ∀ i, MvPolynomial.aeval x (w i) = v i)

/-- Cache the coefficient-ring instance for the ambient tensor map. -/
local instance specializationEvaluationCoefficientsRing : CommRing (Coefficients R I d) :=
  inferInstance
/-- Cache the chart-ring instance for the ambient tensor map. -/
local instance specializationEvaluationChartRing : CommRing (ChartRing R I d w) :=
  inferInstance

/-- The ambient polynomial map of the actual chart family over the test ring. -/
def specializedChartEvaluation :
    let _ := chartSpecializationScalars R I d v x w hw
    MvPolynomial I S →ₐ[S] S ⊗[ChartRing R I d w] ChartAlgebra R I d w := by
  let _ := chartSpecializationScalars R I d v x w hw
  exact MvPolynomial.aeval fun i ↦
    (1 : S) ⊗ₜ[ChartRing R I d w] chartInclusion R I d w (generator R I d i)

/-- Reconstruction preserves original ambient polynomials. -/
theorem chartSpecializationEquiv_polynomial (p : MvPolynomial I R) :
    let _ := chartSpecializationScalars R I d v x w hw
    chartSpecializationEquiv R I d v x w hw
      (1 ⊗ₜ chartEvaluation R I d w (chartPolynomial R I d w p)) =
        MvPolynomial.aeval x p := by
  let _ := chartSpecializationScalars R I d v x w hw
  dsimp only
  rw [chartEvaluation_polynomial, chartSpecializationEquiv_inclusion, realization_evaluation]

/-- Reconstruction identifies the entire ambient quotient map over the test ring. -/
theorem chartSpecializationEquiv_evaluation :
    let _ := chartSpecializationScalars R I d v x w hw
    (chartSpecializationEquiv R I d v x w hw).toAlgHom.comp
      (specializedChartEvaluation R I d v x w hw) = MvPolynomial.aeval x := by
  let _ := chartSpecializationScalars R I d v x w hw
  apply MvPolynomial.algHom_ext
  intro i
  change chartSpecializationEquiv R I d v x w hw
    (specializedChartEvaluation R I d v x w hw (MvPolynomial.X i)) = _
  rw [specializedChartEvaluation, MvPolynomial.aeval_X,
    chartSpecializationEquiv_inclusion, realization_generator, MvPolynomial.aeval_X]

/-- The specialized chart and the given quotient have exactly the same ambient ideal. -/
theorem specializedChartEvaluation_ker :
    RingHom.ker (specializedChartEvaluation R I d v x w hw).toRingHom =
      RingHom.ker (MvPolynomial.aeval x : MvPolynomial I S →ₐ[S] A).toRingHom := by
  let _ := chartSpecializationScalars R I d v x w hw
  ext p
  change specializedChartEvaluation R I d v x w hw p = 0 ↔ MvPolynomial.aeval x p = 0
  have h := AlgHom.congr_fun (chartSpecializationEquiv_evaluation R I d v x w hw) p
  change chartSpecializationEquiv R I d v x w hw
    (specializedChartEvaluation R I d v x w hw p) = MvPolynomial.aeval x p at h
  rw [← h, map_eq_zero_iff _ (chartSpecializationEquiv R I d v x w hw).injective]

end FLT.Mazur.HilbertChart
