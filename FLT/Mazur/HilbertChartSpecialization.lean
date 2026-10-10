/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartAlgebraSpecialization
public import FLT.Mazur.HilbertChartClassifyingMap
public import FLT.Mazur.HilbertChartBasisAlgebra
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Reconstruction from the prescribed-basis chart

The actual iterated scalar extension over the chart ring cancels to the
coefficient-ring scalar extension, and hence reconstructs the given based algebra.
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

/-- Cache the coefficient-ring instance for nested scalar extensions. -/
local instance chartSpecializationCoefficientsRing : CommRing (Coefficients R I d) :=
  inferInstance
/-- Cache the chart-ring instance for nested scalar extensions. -/
local instance chartSpecializationChartRing : CommRing (ChartRing R I d w) := inferInstance

/-- The scalar action defined by the actual classifying map. -/
abbrev chartSpecializationScalars : Algebra (ChartRing R I d w) S :=
  (classifyingMap R I d v x w hw).toRingHom.toAlgebra

/-- The two parameter actions agree by the proved factorization through the chart. -/
theorem chartSpecializationTower :
    let _ := specializationScalars R I d v x
    let _ := chartSpecializationScalars R I d v x w hw
    IsScalarTower (Coefficients R I d) (ChartRing R I d w) S := by
  let _ := specializationScalars R I d v x
  let _ := chartSpecializationScalars R I d v x w hw
  exact IsScalarTower.of_algebraMap_eq fun a ↦
    (classifyingMap_chartMap R I d v x w hw a).symm

/-- Cancellation of the actual intermediate chart scalar extension. -/
def chartSpecializationCancel :
    let _ := specializationScalars R I d v x
    let _ := chartSpecializationScalars R I d v x w hw
    S ⊗[ChartRing R I d w] ChartAlgebra R I d w ≃ₐ[S]
      S ⊗[Coefficients R I d] UniversalAlgebra R I d := by
  let _ := specializationScalars R I d v x
  let _ := chartSpecializationScalars R I d v x w hw
  let _ := chartSpecializationTower R I d v x w hw
  exact Algebra.TensorProduct.cancelBaseChange (Coefficients R I d)
    (ChartRing R I d w) S S (UniversalAlgebra R I d)

/-- The prescribed-basis chart family specializes to the original based algebra. -/
def chartSpecializationEquiv :
    let _ := chartSpecializationScalars R I d v x w hw
    S ⊗[ChartRing R I d w] ChartAlgebra R I d w ≃ₐ[S] A := by
  let _ := specializationScalars R I d v x
  let _ := chartSpecializationScalars R I d v x w hw
  exact (chartSpecializationCancel R I d v x w hw).trans (specializationEquiv R I d v x)

/-- Reconstruction on a pure universal vector is the original realization. -/
theorem chartSpecializationEquiv_inclusion (a : UniversalAlgebra R I d) :
    let _ := chartSpecializationScalars R I d v x w hw
    chartSpecializationEquiv R I d v x w hw (1 ⊗ₜ chartInclusion R I d w a) =
      realization R I d v x a := by
  let _ := specializationScalars R I d v x
  let _ := chartSpecializationScalars R I d v x w hw
  let _ := chartSpecializationTower R I d v x w hw
  let _ := specializationTargetScalars R I d v x
  let _ : IsScalarTower (Coefficients R I d) S A :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  change specializationMap R I d v x
    (Algebra.TensorProduct.cancelBaseChange (Coefficients R I d)
      (ChartRing R I d w) S S (UniversalAlgebra R I d) (1 ⊗ₜ (1 ⊗ₜ a))) = _
  rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul,
    specializationMap, AlgHom.liftEquiv_tmul, one_smul]
  rfl

/-- Reconstruction preserves the distinguished prescribed-polynomial basis. -/
theorem chartSpecializationEquiv_basis (i : Fin d) :
    let _ := chartSpecializationScalars R I d v x w hw
    chartSpecializationEquiv R I d v x w hw (1 ⊗ₜ chartBasis R I d w i) = v i := by
  let _ := chartSpecializationScalars R I d v x w hw
  dsimp only
  rw [chartBasis, Module.Basis.baseChange_apply]
  change chartSpecializationEquiv R I d v x w hw
    (1 ⊗ₜ chartInclusion R I d w (basis R I d i)) = _
  rw [chartSpecializationEquiv_inclusion, realization_basis]

end FLT.Mazur.HilbertChart
