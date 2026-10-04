/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.AugmentationTangentRelations

/-! # Flat tensoring of actual augmentation tangents and their cotangent pairing -/

@[expose] public noncomputable section
open TensorProduct
namespace AlgHom
variable {R A M T : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [AddCommGroup T] [Module R T]
  [Module.Free R A] [Module.Finite R A] [Module.Flat R T] (ε : A →ₐ[R] R)

/-- Actual tangents commute with flat tensoring, without projectivity of the cotangent. -/
def flatAugmentationTangentEquiv :
    T ⊗[R] ε.augmentationTangent (M := M) ≃ₗ[R]
      ε.augmentationTangent (M := T ⊗[R] M) :=
  (TensorProduct.congr (LinearEquiv.refl R T) ε.augmentationTangentRelationEquiv).trans
    ((LinearMap.flatTensorHomKernelEquiv ε.augmentationRelation).trans
      ε.augmentationTangentRelationEquiv.symm)

/-- Flat comparison evaluates on the same original coordinates. -/
theorem flatAugmentationTangentEquiv_tmul (t : T) (d : ε.augmentationTangent (M := M))
    (a : A) :
    (ε.flatAugmentationTangentEquiv (t ⊗ₜ[R] d)).val a = t ⊗ₜ[R] d.val a := by
  change (LinearMap.flatTensorHomKernelEquiv ε.augmentationRelation
    (t ⊗ₜ[R] ε.augmentationTangentRelationEquiv d)).val a = _
  exact LinearMap.flatTensorHomKernelEquiv_tmul _ _ _ _

/-- The corresponding Hom comparison uses the original cotangent quotient. -/
def flatCotangentHomEquiv :
    T ⊗[R] ((RingHom.ker ε).Cotangent →ₗ[R] M) ≃ₗ[R]
      ((RingHom.ker ε).Cotangent →ₗ[R] T ⊗[R] M) :=
  (TensorProduct.congr (LinearEquiv.refl R T) ε.augmentationTangentEquiv).trans
    (ε.flatAugmentationTangentEquiv.trans ε.augmentationTangentEquiv.symm)

/-- The comparison respects the original cotangent pairing, at every cotangent element. -/
theorem flatCotangentHomEquiv_tmul (t : T) (f : (RingHom.ker ε).Cotangent →ₗ[R] M)
    (a : (RingHom.ker ε).Cotangent) :
    ε.flatCotangentHomEquiv (t ⊗ₜ[R] f) a = t ⊗ₜ[R] f a := by
  obtain ⟨b, rfl⟩ := (RingHom.ker ε).toCotangent_surjective a
  change (ε.augmentationTangentEquiv.symm
    (ε.flatAugmentationTangentEquiv (t ⊗ₜ[R] ε.augmentationTangentEquiv f)))
    ((RingHom.ker ε).toCotangent b) = _
  have he := congrArg (fun d : ε.augmentationTangent (M := T ⊗[R] M) ↦ d.val (b : A))
    (ε.augmentationTangentEquiv.apply_symm_apply
      (ε.flatAugmentationTangentEquiv (t ⊗ₜ[R] ε.augmentationTangentEquiv f)))
  rw [augmentationTangentEquiv_apply, augmentationCotangent_of_mem] at he
  rw [he, flatAugmentationTangentEquiv_tmul, augmentationTangentEquiv_apply,
    augmentationCotangent_of_mem]

end AlgHom
