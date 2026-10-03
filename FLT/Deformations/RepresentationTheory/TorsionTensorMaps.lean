/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.PrimePowerExact
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic

/-!
# Maps on the original quotient tensor levels

The coefficient inclusion and reduction act on `(R/(a^n)) ⊗[R] V`.
They commute with every original linear operator, including Galois actions.
-/

@[expose] public noncomputable section
open scoped TensorProduct

namespace GaloisRepresentation.PrimePower
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The original tensor module at a principal power level. -/
abbrev Level (a : R) (n : ℕ) := Quot a n ⊗[R] V

/-- Multiplication-induced inclusion on the original tensor modules. -/
def tensorInclusion (a : R) (m n : ℕ) :
    Level (V := V) a m →ₗ[R] Level (V := V) a (m + n) :=
  (inclusion a m n).rTensor V

/-- Reduction on the original tensor modules. -/
def tensorReduction (a : R) (m n : ℕ) :
    Level (V := V) a (m + n) →ₗ[R] Level (V := V) a n :=
  (reduction a m n).rTensor V

/-- Inclusion commutes with each operator of the original representation. -/
theorem tensorInclusion_natural (a : R) (m n : ℕ) (f : V →ₗ[R] V)
    (x : Level (V := V) a m) :
    tensorInclusion a m n (f.baseChange (Quot a m) x) =
      f.baseChange (Quot a (m + n)) (tensorInclusion a m n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Reduction commutes with each operator of the original representation. -/
theorem tensorReduction_natural (a : R) (m n : ℕ) (f : V →ₗ[R] V)
    (x : Level (V := V) a (m + n)) :
    tensorReduction a m n (f.baseChange (Quot a (m + n)) x) =
      f.baseChange (Quot a n) (tensorReduction a m n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Tensor reduction is surjective without a flatness assumption. -/
theorem tensorReduction_surjective (a : R) (m n : ℕ) :
    Function.Surjective (tensorReduction (V := V) a m n) :=
  LinearMap.rTensor_surjective V (reduction_surjective a m n)

/-- These are the actual exact tensor level maps. -/
theorem tensor_exact (a : R) (m n : ℕ) :
    Function.Exact (tensorInclusion (V := V) a m n) (tensorReduction a m n) :=
  rTensor_exact V (exact a m n) (reduction_surjective a m n)

/-- A flat original module preserves the injective principal-power inclusion. -/
theorem tensorInclusion_injective [IsDomain R] [Module.Flat R V]
    {a : R} (ha : a ≠ 0) (m n : ℕ) :
    Function.Injective (tensorInclusion (V := V) a m n) :=
  Module.Flat.rTensor_preserves_injective_linearMap _ (inclusion_injective ha m n)

end GaloisRepresentation.PrimePower
