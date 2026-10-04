/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleInfinitesimalFlatCover
public import FLT.GroupScheme.AugmentationKernelNaturality
public import FLT.GroupScheme.PointDifferenceCotangentEvaluation

/-! # Pullback of actual infinitesimal points along maps of covers -/

@[expose] public noncomputable section
open scoped TensorProduct
open ThreeAdicPlan.PDivisibleSystem
namespace AlgHom
variable {R A B C D E : Type} [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [CommRing D] [CommRing E] [Algebra R A] [Algebra R B]
  [Algebra B C] [Algebra B D] [Algebra R D] [IsScalarTower R B D]
  [Algebra B E] [Algebra R E] [IsScalarTower R B E]
  (ε : A →ₐ[R] R)

/-- A map of covers pulls an actual augmentation point back along its specified ring map. -/
def coverAugmentationPointMap (β : D →ₐ[B] E)
    (f : ε.AugmentationPointKernel (coverPointReduction (R := R) (B := B) (C := C) (D := D))) :
    ε.AugmentationPointKernel (coverPointReduction (R := R) (B := B) (C := C) (D := E)) :=
  augmentationKernelMap _ _ (β.restrictScalars R)
    ((Algebra.TensorProduct.map β (AlgHom.id B C)).restrictScalars R)
    (by ext d; simp) ε f

end AlgHom
