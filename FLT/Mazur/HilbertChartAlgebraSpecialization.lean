/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartAlgebraRealization
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Actual specialization of the universal based algebra

After scalar extension along the extracted coefficient map, the universal
algebra is isomorphic to the original based algebra. The proof uses the actual
base-changed basis and the realization map, and includes rank zero.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable {S A : Type*} [CommRing S] [CommRing A] [Algebra R S] [Algebra S A]
variable [Algebra R A] [IsScalarTower R S A]
variable (v : Module.Basis (Fin d) S A) (x : I → A)

/-- Cache the coefficient-ring instance for nested tensor inference. -/
local instance specializationCoefficientsRing : CommRing (Coefficients R I d) := inferInstance

/-- Scalar extension uses the extracted coefficient map. -/
abbrev specializationScalars : Algebra (Coefficients R I d) S :=
  (readCoefficients R I d v x).toRingHom.toAlgebra

/-- The target algebra carries the same extracted coefficient action. -/
abbrev specializationTargetScalars : Algebra (Coefficients R I d) A :=
  Algebra.compHom A (readCoefficients R I d v x).toRingHom

/-- Realization is also linear over the extracted universal coefficient action. -/
def realizationOverCoefficients :
    let _ := specializationTargetScalars R I d v x
    UniversalAlgebra R I d →ₐ[Coefficients R I d] A := by
  let _ := specializationTargetScalars R I d v x
  refine {
  __ := (realization R I d v x).toRingHom
  commutes' := ?_ }
  intro q
  apply v.ext_elem
  intro k
  change v.repr (realizeVector R I d v x _) k = _
  rw [realizeVector_repr, Algebra.algebraMap_eq_smul_one]
  change readCoefficients R I d v x (q * unitCoeff R I d k) =
    v.repr (algebraMap S A (readCoefficients R I d v x q)) k
  rw [map_mul, readCoefficients_unit, Algebra.algebraMap_eq_smul_one]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, structureUnit]

/-- The actual map from the scalar extension of the universal algebra. -/
def specializationMap :
    let _ := specializationScalars R I d v x
    S ⊗[Coefficients R I d] UniversalAlgebra R I d →ₐ[S] A := by
  let _ := specializationScalars R I d v x
  let _ := specializationTargetScalars R I d v x
  let _ : IsScalarTower (Coefficients R I d) S A :=
    IsScalarTower.of_algebraMap_eq (R := Coefficients R I d) (S := S) (A := A) fun _ ↦ rfl
  exact AlgHom.liftEquiv (Coefficients R I d) S (UniversalAlgebra R I d) A
    (realizationOverCoefficients R I d v x)

/-- Every base-changed universal basis vector maps to the given basis vector. -/
theorem specializationMap_basis (i : Fin d) :
    let _ := specializationScalars R I d v x
    specializationMap R I d v x ((basis R I d).baseChange S i) = v i := by
  let _ := specializationScalars R I d v x
  let _ := specializationTargetScalars R I d v x
  let _ : IsScalarTower (Coefficients R I d) S A :=
    IsScalarTower.of_algebraMap_eq (R := Coefficients R I d) (S := S) (A := A) fun _ ↦ rfl
  change specializationMap R I d v x ((basis R I d).baseChange S i) = v i
  rw [Module.Basis.baseChange_apply, specializationMap, AlgHom.liftEquiv_tmul, one_smul]
  exact realization_basis R I d v x i

/-- The actual specialization map is bijective because it takes a basis to a basis. -/
theorem specializationMap_bijective : Function.Bijective (specializationMap R I d v x) := by
  let _ := specializationScalars R I d v x
  let b := (basis R I d).baseChange S
  let e := b.equiv v (Equiv.refl (Fin d))
  have h : (specializationMap R I d v x).toLinearMap = e.toLinearMap := by
    apply b.ext
    intro i
    exact (specializationMap_basis R I d v x i).trans
      (Module.Basis.equiv_apply b i v (Equiv.refl (Fin d))).symm
  have hf : (specializationMap R I d v x : _ → A) = e :=
    congrArg (fun f : (S ⊗[Coefficients R I d] UniversalAlgebra R I d) →ₗ[S] A ↦ ⇑f) h
  rw [hf]
  exact e.bijective

/-- The original based algebra is the actual scalar extension of the universal algebra. -/
def specializationEquiv :
    let _ := specializationScalars R I d v x
    S ⊗[Coefficients R I d] UniversalAlgebra R I d ≃ₐ[S] A := by
  let _ := specializationScalars R I d v x
  exact AlgEquiv.ofBijective (specializationMap R I d v x) (specializationMap_bijective R I d v x)

end FLT.Mazur.HilbertChart
