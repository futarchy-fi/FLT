/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleInfinitesimalFlatCover
public import FLT.GroupScheme.InfinitesimalTangentCocycle

/-! # Actual overlap points of a local lift have the same reduction -/

@[expose] public noncomputable section
open scoped TensorProduct
open ThreeAdicPlan.PDivisibleSystem
namespace Algebra
variable {R A B C D E : Type} [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [CommRing D] [CommRing E] [Algebra R A] [Algebra R B]
  [Algebra B C] [Algebra R C] [IsScalarTower R B C]
  [Algebra B D] [Algebra R D] [IsScalarTower R B D]
  [Algebra B E] [Algebra R E] [IsScalarTower R B E]

/-- Every map of covers preserves the prescribed reduction of an actual local point. -/
theorem cover_point_reduction_postcomp (β : D →ₐ[B] E)
    (x : A →ₐ[R] C) (y : A →ₐ[R] D)
    (hy : (coverPointReduction (R := R) (B := B) (C := C) (D := D)).comp y =
      (TensorProduct.includeRight.restrictScalars R).comp x) :
    (coverPointReduction (R := R) (B := B) (C := C) (D := E)).comp ((β.restrictScalars R).comp y) =
      (TensorProduct.includeRight.restrictScalars R).comp x := by
  ext a
  have h := congrArg (TensorProduct.map β (AlgHom.id B C)) (AlgHom.congr_fun hy a)
  simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    TensorProduct.includeLeft_apply, TensorProduct.includeRight_apply,
    TensorProduct.map_tmul, map_one, AlgHom.id_apply] using h

/-- The two pullbacks of the constructed local point agree after reduction. -/
theorem cover_point_overlap_reduction (x : A →ₐ[R] C) (y : A →ₐ[R] D)
    (hy : (coverPointReduction (R := R) (B := B) (C := C) (D := D)).comp y =
      (TensorProduct.includeRight.restrictScalars R).comp x) :
    (coverPointReduction (R := R) (B := B) (C := C) (D := D ⊗[B] D)).comp
        (((TensorProduct.includeLeft : D →ₐ[B] D ⊗[B] D).restrictScalars R).comp y) =
      (coverPointReduction (R := R) (B := B) (C := C) (D := D ⊗[B] D)).comp
        (((TensorProduct.includeRight : D →ₐ[B] D ⊗[B] D).restrictScalars R).comp y) :=
  (cover_point_reduction_postcomp (TensorProduct.includeLeft : D →ₐ[B] D ⊗[B] D) x y hy).trans
    (cover_point_reduction_postcomp (TensorProduct.includeRight : D →ₐ[B] D ⊗[B] D) x y hy).symm

end Algebra
