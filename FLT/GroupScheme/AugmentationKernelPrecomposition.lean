/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SquareZeroAugmentationPoints

/-! # Original source maps act compatibly on augmentation points and tangents -/

@[expose] public noncomputable section
namespace AlgHom
variable {R A A' B C M : Type*} [CommRing R] [CommRing A] [CommRing A']
  [CommRing B] [CommRing C] [Algebra R A] [Algebra R A'] [Algebra R B] [Algebra R C]
  [AddCommGroup M] [Module R M]
  (ε : A →ₐ[R] R) (ε' : A' →ₐ[R] R) (f : A' →ₐ[R] A) (hf : ε.comp f = ε')

/-- Precomposition along an actual augmentation-preserving coordinate map. -/
def augmentationKernelPrecomp (q : B →ₐ[R] C) :
    ε.AugmentationPointKernel q → ε'.AugmentationPointKernel q := fun x ↦
  ⟨x.val.comp f, by rw [← comp_assoc, x.property, comp_assoc, hf]⟩

/-- The same coordinate map on module-valued tangents. -/
def augmentationTangentPrecomp :
    ε.augmentationTangent (M := M) →ₗ[R] ε'.augmentationTangent (M := M) where
  toFun d := ⟨d.val.comp f.toLinearMap, by
    intro a b
    change d.val (f (a * b)) = _
    rw [map_mul, d.property]
    change ε (f a) • d.val (f b) + ε (f b) • d.val (f a) = _
    rw [show ε (f a) = ε' a from AlgHom.congr_fun hf a,
      show ε (f b) = ε' b from AlgHom.congr_fun hf b]
    rfl⟩
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

/-- Tangent extraction retains the specified coordinate map. -/
theorem augmentationPointToTangent_precomp (q : B →ₐ[R] C)
    (hJ : RingHom.ker q ^ 2 = ⊥) (x : ε.AugmentationPointKernel q) :
    augmentationPointToTangent ε' q hJ (augmentationKernelPrecomp ε ε' f hf q x) =
      augmentationTangentPrecomp ε ε' f hf (augmentationPointToTangent ε q hJ x) := by
  apply Subtype.ext
  ext a
  change x.val (f a) - algebraMap R B (ε' a) =
    x.val (f a) - algebraMap R B (ε (f a))
  rw [show ε (f a) = ε' a from AlgHom.congr_fun hf a]

/-- Reconstruction commutes with the same original coordinate map. -/
theorem tangentToAugmentationPoint_precomp (q : B →ₐ[R] C)
    (hJ : RingHom.ker q ^ 2 = ⊥) (d : ε.augmentationTangent (M := RingHom.ker q)) :
    tangentToAugmentationPoint ε' q hJ (augmentationTangentPrecomp ε ε' f hf d) =
      augmentationKernelPrecomp ε ε' f hf q (tangentToAugmentationPoint ε q hJ d) := by
  apply Subtype.ext
  ext a
  change algebraMap R B (ε' a) + (d.val (f a) : B) =
    algebraMap R B (ε (f a)) + (d.val (f a) : B)
  rw [show ε (f a) = ε' a from AlgHom.congr_fun hf a]

end AlgHom
