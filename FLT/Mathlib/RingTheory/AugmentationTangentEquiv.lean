/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.AugmentationTangent

/-! # The actual cotangent quotient represents tangent functionals -/

@[expose] public noncomputable section
namespace AlgHom
variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] (ε : A →ₐ[R] R)

/-- A linear map from the actual cotangent quotient induces a tangent functional. -/
def cotangentToAugmentationTangent :
    ((RingHom.ker ε).Cotangent →ₗ[R] M) →ₗ[R] ε.augmentationTangent (M := M) where
  toFun f := ⟨f.comp ε.augmentationCotangent, by
    intro a b
    change f (ε.augmentationCotangent (a * b)) = _
    rw [augmentationCotangent_mul, map_add, map_smul, map_smul]
    rfl⟩
  map_add' f g := by apply Subtype.ext; ext a; rfl
  map_smul' r f := by apply Subtype.ext; ext a; rfl

/-- Cotangent maps are uniquely determined by their actual augmented derivatives. -/
theorem cotangentToAugmentationTangent_injective :
    Function.Injective (ε.cotangentToAugmentationTangent (M := M)) := by
  intro f g h
  ext a
  obtain ⟨b, rfl⟩ := (RingHom.ker ε).toCotangent_surjective a
  have he := congrArg (fun d : ε.augmentationTangent (M := M) ↦ d.val b) h
  change f (ε.augmentationCotangent b) = g (ε.augmentationCotangent b) at he
  simpa only [augmentationCotangent_of_mem] using he

/-- Every actual Leibniz functional descends uniquely through the cotangent quotient. -/
theorem cotangentToAugmentationTangent_surjective :
    Function.Surjective (ε.cotangentToAugmentationTangent (M := M)) := by
  intro d
  refine ⟨augmentationTangentToCotangent d, ?_⟩
  apply Subtype.ext
  ext a
  exact augmentationTangentToCotangent_projection d a

/-- The actual tangent-cotangent duality, valid for arbitrary module-valued tangents. -/
def augmentationTangentEquiv :
    ((RingHom.ker ε).Cotangent →ₗ[R] M) ≃ₗ[R] ε.augmentationTangent (M := M) :=
  LinearEquiv.ofBijective ε.cotangentToAugmentationTangent
    ⟨ε.cotangentToAugmentationTangent_injective, ε.cotangentToAugmentationTangent_surjective⟩

/-- The equivalence evaluates by the original augmentation projection. -/
theorem augmentationTangentEquiv_apply (f : (RingHom.ker ε).Cotangent →ₗ[R] M) (a : A) :
    (ε.augmentationTangentEquiv f).val a = f (ε.augmentationCotangent a) := rfl

end AlgHom
