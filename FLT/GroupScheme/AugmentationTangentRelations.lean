/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FlatTensorHomKernel
public import FLT.Mathlib.RingTheory.AugmentationTangentEquiv
public import Mathlib.Algebra.Algebra.Bilinear

/-! # The original Leibniz relations present augmentation tangents -/

@[expose] public noncomputable section
open TensorProduct
namespace AlgHom
variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] (ε : A →ₐ[R] R)

/-- The relation in the original coordinate module expressing Leibniz at the augmentation. -/
def augmentationRelation : A ⊗[R] A →ₗ[R] A :=
  LinearMap.mul' R A -
    (TensorProduct.lid R A).toLinearMap.comp (ε.toLinearMap.rTensor A) -
    (TensorProduct.rid R A).toLinearMap.comp (ε.toLinearMap.lTensor A)

/-- Evaluation of the relation on original coordinates. -/
theorem augmentationRelation_tmul (a b : A) :
    ε.augmentationRelation (a ⊗ₜ[R] b) = a * b - ε a • b - ε b • a := by
  simp [augmentationRelation]

/-- A functional kills the relation map exactly when it is an original augmentation tangent. -/
theorem augmentationTangent_eq_ker_relation :
    ε.augmentationTangent (M := M) = LinearMap.ker ε.augmentationRelation.relationPrecomp := by
  ext d
  change (∀ a b, d (a * b) = ε a • d b + ε b • d a) ↔
    d.comp ε.augmentationRelation = 0
  constructor
  · intro hd
    apply TensorProduct.ext'
    intro a b
    change d (ε.augmentationRelation (a ⊗ₜ[R] b)) = 0
    simp only [augmentationRelation_tmul, map_sub, map_smul, hd]
    abel
  · intro hd a b
    have h := LinearMap.congr_fun hd (a ⊗ₜ[R] b)
    simp only [LinearMap.comp_apply, augmentationRelation_tmul, map_sub, map_smul,
      LinearMap.zero_apply] at h
    rw [sub_sub, sub_eq_zero] at h
    exact h

/-- Identify the actual tangent submodule with this relation kernel. -/
def augmentationTangentRelationEquiv :
    ε.augmentationTangent (M := M) ≃ₗ[R]
      LinearMap.ker (ε.augmentationRelation.relationPrecomp (M := M)) :=
  LinearEquiv.ofEq _ _ ε.augmentationTangent_eq_ker_relation

end AlgHom
