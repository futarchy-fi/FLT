/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfPointFiberDescent
public import Mathlib.Algebra.Algebra.Operations

/-!
# Homogeneous submodules of the actual quotient fibre

The degree is an element of the augmentation kernel algebra. Multiplication
respects degrees, and faithful flat descent identifies degree one with scalars.
This does not assert that all degree components are invertible.
-/

@[expose] public noncomputable section

open scoped TensorProduct
namespace HopfAlgebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra B A] [IsScalarTower R B A]
  (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
  (p : B →ₐ[R] R)

/-- Functions whose actual kernel coaction has the specified degree. -/
def pointFiberHomogeneous (t : A ⧸ augmentationIdeal f) :
    Submodule R (PointFiber (A := A) p) where
  carrier := {z | pointFiberCoaction f hf p z = z ⊗ₜ[R] t}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change pointFiberCoaction f hf p x = x ⊗ₜ[R] t at hx
    change pointFiberCoaction f hf p y = y ⊗ₜ[R] t at hy
    change pointFiberCoaction f hf p (x + y) = _
    rw [map_add, hx, hy, TensorProduct.add_tmul]
  smul_mem' := by
    intro r x hx
    change pointFiberCoaction f hf p x = x ⊗ₜ[R] t at hx
    change pointFiberCoaction f hf p (r • x) = _
    rw [map_smul, hx, TensorProduct.smul_tmul']

/-- Membership uses the constructed coaction, not a supplied grading. -/
@[simp] theorem mem_pointFiberHomogeneous (t : A ⧸ augmentationIdeal f)
    (z : PointFiber (A := A) p) :
    z ∈ pointFiberHomogeneous f hf p t ↔ pointFiberCoaction f hf p z = z ⊗ₜ[R] t :=
  Iff.rfl

/-- Multiplying homogeneous functions multiplies their degrees. -/
theorem pointFiberHomogeneous_mul_le (s t : A ⧸ augmentationIdeal f) :
    pointFiberHomogeneous f hf p s * pointFiberHomogeneous f hf p t ≤
      pointFiberHomogeneous f hf p (s * t) := by
  apply Submodule.mul_le.mpr
  intro x hx y hy
  change pointFiberCoaction f hf p (x * y) = _
  rw [map_mul, hx, hy, Algebra.TensorProduct.tmul_mul_tmul]

variable [Module.FaithfullyFlat B A]

/-- The identity-degree component is exactly the scalar submodule. -/
@[simp] theorem pointFiberHomogeneous_one :
    pointFiberHomogeneous f hf p 1 = 1 := by
  rw [Submodule.one_eq_range]
  ext z
  exact (pointFiber_invariant_iff f hf p z).symm

/-- Opposite degrees pair into the base ring. -/
theorem pointFiberHomogeneous_mul_inv_le (t : (A ⧸ augmentationIdeal f)ˣ) :
    pointFiberHomogeneous f hf p (t : A ⧸ augmentationIdeal f) *
      pointFiberHomogeneous f hf p (↑t⁻¹) ≤ 1 := by
  have h := pointFiberHomogeneous_mul_le f hf p (t : A ⧸ augmentationIdeal f) (↑t⁻¹)
  simpa using h

/-- For opposite components the remaining strong-grading condition is precisely
that their product contains one. No invertibility is assumed in this equivalence. -/
theorem pointFiberHomogeneous_mul_inv_eq_one_iff (t : (A ⧸ augmentationIdeal f)ˣ) :
    pointFiberHomogeneous f hf p (t : A ⧸ augmentationIdeal f) *
      pointFiberHomogeneous f hf p (↑t⁻¹) = 1 ↔
    (1 : PointFiber (A := A) p) ∈
      pointFiberHomogeneous f hf p (t : A ⧸ augmentationIdeal f) *
        pointFiberHomogeneous f hf p (↑t⁻¹) := by
  constructor
  · intro h; rw [h]; exact Submodule.one_le.mp le_rfl
  · intro h
    exact le_antisymm (pointFiberHomogeneous_mul_inv_le f hf p t)
      (Submodule.one_le.mpr h)

end HopfAlgebra
