/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Module.ULift

/-! # Tensor comparison for independently lifted coefficients and vectors -/

@[expose] public noncomputable section
attribute [local instance 2000] TensorProduct.leftModule
open scoped TensorProduct
universe u v
namespace GaloisRepresentation
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Scalar extension to a lifted coefficient ring is the independently lifted original module. -/
def uliftCoefficientTensor :
    ULift.{u} R ⊗[R] V ≃ₗ[ULift.{u} R] ULift.{v} V := by
  let e : ULift.{u} R ⊗[R] V ≃ₗ[R] ULift.{v} V :=
    ((TensorProduct.congr (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R)
      (LinearEquiv.refl R V)).trans (TensorProduct.lid R V)).trans ULift.moduleEquiv.symm
  refine { e.toAddEquiv with map_smul' := ?_ }
  rintro ⟨a⟩ x
  change e (a • x) = a • e x
  exact e.map_smul a x

/-- The comparison multiplies by the actual coefficient and lifts the result. -/
@[simp] theorem uliftCoefficientTensor_tmul (a : ULift.{u} R) (x : V) :
    uliftCoefficientTensor (a ⊗ₜ[R] x) = (ULift.up (a.down • x) : ULift.{v} V) := rfl

/-- The inverse sends a lifted vector to its actual pure tensor. -/
@[simp] theorem uliftCoefficientTensor_symm_up (x : V) :
    (uliftCoefficientTensor : ULift.{u} R ⊗[R] V ≃ₗ[ULift.{u} R] ULift.{v} V).symm
      (ULift.up x) = 1 ⊗ₜ[R] x := by
  apply uliftCoefficientTensor.injective
  rw [LinearEquiv.apply_symm_apply, uliftCoefficientTensor_tmul]
  simp

end GaloisRepresentation
