/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartParameterRecovery

/-!
# Base-change naturality of Hilbert-chart classification

The coefficients extracted from the actual tensor base change are the scalar
images of the original coefficients. The same holds for the chart map.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable {S A : Type*} [CommRing S] [CommRing A] [Algebra R S] [Algebra S A]
variable [Algebra R A] [IsScalarTower R S A]
variable (v : Module.Basis (Fin d) S A) (x : I → A)
variable (T : Type*) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- The ambient generators in the actual scalar extension. -/
def baseChangedGenerator (i : I) : T ⊗[S] A := 1 ⊗ₜ x i

/-- Multiplication coordinates commute with arbitrary scalar extension. -/
theorem structureCoeff_baseChange (i j k : Fin d) :
    structureCoeff (A := T ⊗[S] A) (v.baseChange T) i j k =
      algebraMap S T (structureCoeff v i j k) := by
  change (v.baseChange T).repr (v.baseChange T i * v.baseChange T j) k = _
  rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one]
  rfl

/-- Unit coordinates commute with arbitrary scalar extension. -/
theorem structureUnit_baseChange (k : Fin d) :
    structureUnit (A := T ⊗[S] A) (v.baseChange T) k = algebraMap S T (structureUnit v k) := by
  change (v.baseChange T).repr (1 ⊗ₜ (1 : A)) k = _
  rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  rfl

/-- Generator coordinates commute with arbitrary scalar extension. -/
theorem generatorCoordinates_baseChange (i : I) (k : Fin d) :
    (v.baseChange T).repr (baseChangedGenerator I x T i) k = algebraMap S T (v.repr (x i) k) := by
  rw [baseChangedGenerator, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

omit [Algebra R A] [IsScalarTower R S A] in
/-- Extracting all ring-law parameters commutes with arbitrary scalar extension. -/
theorem readCoefficients_baseChange :
    readCoefficients R I d (A := T ⊗[S] A) (v.baseChange T) (baseChangedGenerator I x T) =
      (IsScalarTower.toAlgHom R S T).comp (readCoefficients R I d v x) := by
  apply coefficientMap_ext
  · intro i j k
    rw [readCoefficients_mul, structureCoeff_baseChange, AlgHom.comp_apply, readCoefficients_mul]
    rfl
  · intro k
    rw [readCoefficients_unit, structureUnit_baseChange, AlgHom.comp_apply, readCoefficients_unit]
    rfl
  · intro i k
    rw [readCoefficients_generator, generatorCoordinates_baseChange,
      AlgHom.comp_apply, readCoefficients_generator]
    rfl

/-- Original ambient evaluation commutes with the actual scalar-extension map. -/
theorem baseChangedGenerator_evaluation (p : MvPolynomial I R) :
    MvPolynomial.aeval (baseChangedGenerator I x T) p = (1 : T) ⊗ₜ[S] MvPolynomial.aeval x p := by
  exact (MvPolynomial.comp_aeval_apply (B := T ⊗[S] A) x
    (Algebra.TensorProduct.includeRight.restrictScalars R) p).symm

variable (w : Fin d → MvPolynomial I R)
variable (hw : ∀ i, MvPolynomial.aeval x (w i) = v i)

include hw in
/-- The prescribed polynomial basis persists under arbitrary base change. -/
theorem baseChangedGenerator_basis (i : Fin d) :
    MvPolynomial.aeval (baseChangedGenerator I x T) (w i) = v.baseChange T i := by
  rw [baseChangedGenerator_evaluation, hw, Module.Basis.baseChange_apply]

/-- Classification of arbitrary based quotient algebras is natural in the test ring. -/
theorem classifyingMap_baseChange :
    classifyingMap R I d (A := T ⊗[S] A) (v.baseChange T) (baseChangedGenerator I x T) w
      (baseChangedGenerator_basis R I d v x T w hw) =
        (IsScalarTower.toAlgHom R S T).comp (classifyingMap R I d v x w hw) := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro a
  exact AlgHom.congr_fun (readCoefficients_baseChange R I d v x T) a

end FLT.Mazur.HilbertChart
