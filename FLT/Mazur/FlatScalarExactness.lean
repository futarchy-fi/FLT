/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Scalar exact sequences on flat modules

An exact pair of scalar multiplications on a ring stays exact on any flat
module. The resulting first-isomorphism comparison identifies the quotient
by the first scalar with the image of the second scalar.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FlatScalarExactness

variable {R : Type*} [CommRing R]
  (M : Type*) [AddCommGroup M] [Module R M] [Module.Flat R M]

/-- Flatness transports exact scalar multiplication sequences to the module. -/
theorem scalar_exact (a b : R)
    (h : Function.Exact (DistribSMul.toLinearMap R R a)
      (DistribSMul.toLinearMap R R b)) :
    Function.Exact (DistribSMul.toLinearMap R M a) (DistribSMul.toLinearMap R M b) := by
  have ht := Module.Flat.rTensor_exact M h
  rw [LinearMap.rTensor_smul_action, LinearMap.rTensor_smul_action] at ht
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := TensorProduct.lid R M) (e₂ := TensorProduct.lid R M)
    (e₃ := TensorProduct.lid R M) _ _ ht
  · apply LinearMap.ext
    intro x
    exact ((TensorProduct.lid R M).map_smul a x).symm
  · apply LinearMap.ext
    intro x
    exact ((TensorProduct.lid R M).map_smul b x).symm

/-- A scalar-kernel identity holds in every flat module over the same ring. -/
theorem smul_eq_zero_iff (a b : R)
    (h : ∀ r : R, b * r = 0 ↔ ∃ s, a * s = r) (x : M) :
    b • x = 0 ↔ ∃ y : M, a • y = x :=
  scalar_exact M a b h x

/-- The scalar quotient is the actual image of the next scalar multiplication. -/
def quotientEquivRange (a b : R)
    (h : ∀ r : R, b * r = 0 ↔ ∃ s, a * s = r) :
    (M ⧸ LinearMap.range (DistribSMul.toLinearMap R M a)) ≃ₗ[R]
      LinearMap.range (DistribSMul.toLinearMap R M b) :=
  (Submodule.quotEquivOfEq _ _ (scalar_exact M a b h).linearMap_ker_eq.symm).trans
    (DistribSMul.toLinearMap R M b).quotKerEquivRange

/-- The quotient-to-image comparison sends a class to its scalar multiple. -/
theorem quotientEquivRange_mk (a b : R)
    (h : ∀ r : R, b * r = 0 ↔ ∃ s, a * s = r) (x : M) :
    (quotientEquivRange M a b h (Submodule.Quotient.mk x) : M) = b • x := rfl

end FLT.Mazur.FlatScalarExactness
