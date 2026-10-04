/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RelativeFlatHomKernel
public import FLT.GroupScheme.AugmentationTangentRelations

/-! # Original cotangent functionals commute with flat covers of test algebras -/

@[expose] public noncomputable section
open TensorProduct
namespace AlgHom
variable {R A B M : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M] [Module B M]
  [IsScalarTower R B M] (ε : A →ₐ[R] R)

/-- The same original tangents, as a module over their coefficient algebra. -/
def relativeAugmentationTangent : Submodule B (A →ₗ[R] M) where
  carrier := {d | ∀ a b, d (a * b) = ε a • d b + ε b • d a}
  zero_mem' := by simp
  add_mem' hd he := by
    intro a b
    simp only [LinearMap.add_apply, hd a b, he a b, smul_add]
    abel
  smul_mem' s d hd := by
    intro a b
    simp only [LinearMap.smul_apply, hd a b, smul_add, smul_comm s]

/-- Original cotangent duality retains coefficient-algebra linearity. -/
def relativeCotangentTangentEquiv :
    ((RingHom.ker ε).Cotangent →ₗ[R] M) ≃ₗ[B] ε.relativeAugmentationTangent (B := B) (M := M) :=
  LinearEquiv.ofBijective
    { toFun f := ⟨(ε.augmentationTangentEquiv f).val,
        (ε.augmentationTangentEquiv f).property⟩
      map_add' := by intro f g; apply Subtype.ext; rfl
      map_smul' := by intro s f; apply Subtype.ext; ext a; rfl }
    ε.augmentationTangentEquiv.bijective

/-- The original relations cut out the same tangent module over the test algebra. -/
theorem relativeAugmentationTangent_eq_ker :
    ε.relativeAugmentationTangent (B := B) (M := M) =
      LinearMap.ker (ε.augmentationRelation.relativeRelationPrecomp (B := B)) := by
  ext d
  exact SetLike.ext_iff.mp (ε.augmentationTangent_eq_ker_relation (M := M)) d

/-- Cotangent functionals are precisely the original relation functionals, B-linearly. -/
def relativeCotangentRelationEquiv :
    ((RingHom.ker ε).Cotangent →ₗ[R] M) ≃ₗ[B]
      LinearMap.ker (ε.augmentationRelation.relativeRelationPrecomp (B := B) (M := M)) :=
  ε.relativeCotangentTangentEquiv.trans
    (LinearEquiv.ofEq _ _ ε.relativeAugmentationTangent_eq_ker)

variable {S : Type*} [CommRing S] [Algebra B S] [Algebra R S] [IsScalarTower R B S]
  [Module.Flat B S] [Module.Free R A] [Module.Finite R A]

/-- Flat covers of the test algebra commute with the original cotangent Hom module. -/
def relativeFlatCotangentHomEquiv :
    S ⊗[B] ((RingHom.ker ε).Cotangent →ₗ[R] M) ≃ₗ[B]
      ((RingHom.ker ε).Cotangent →ₗ[R] S ⊗[B] M) :=
  (TensorProduct.congr (LinearEquiv.refl B S) ε.relativeCotangentRelationEquiv).trans
    ((LinearMap.relativeFlatHomKernelEquiv ε.augmentationRelation).trans
      ε.relativeCotangentRelationEquiv.symm)

/-- The relative comparison preserves the actual original cotangent pairing. -/
theorem relativeFlatCotangentHomEquiv_tmul (s : S)
    (f : (RingHom.ker ε).Cotangent →ₗ[R] M) (a : (RingHom.ker ε).Cotangent) :
    ε.relativeFlatCotangentHomEquiv (s ⊗ₜ[B] f) a = s ⊗ₜ[B] f a := by
  obtain ⟨b, rfl⟩ := (RingHom.ker ε).toCotangent_surjective a
  let d := LinearMap.relativeFlatHomKernelEquiv ε.augmentationRelation
    (s ⊗ₜ[B] ε.relativeCotangentRelationEquiv f)
  have he := congrArg (fun t ↦ t.val (b : A))
    (ε.relativeCotangentRelationEquiv.apply_symm_apply d)
  change (ε.relativeCotangentRelationEquiv.symm d)
    (ε.augmentationCotangent b) = d.val b at he
  rw [augmentationCotangent_of_mem] at he
  change (ε.relativeCotangentRelationEquiv.symm d) _ = _
  rw [he]
  change (LinearMap.relativeFlatHomKernelEquiv ε.augmentationRelation
    (s ⊗ₜ[B] ε.relativeCotangentRelationEquiv f)).val b = _
  rw [LinearMap.relativeFlatHomKernelEquiv_tmul]
  change s ⊗ₜ[B] f (ε.augmentationCotangent b) = _
  rw [augmentationCotangent_of_mem]

end AlgHom
