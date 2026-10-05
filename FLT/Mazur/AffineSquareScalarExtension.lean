/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineIntegerModel

/-!
# Scalar extension of affine squares

Base change retains every arrow of an affine cartesian square. These lemmas
use tensor products directly, independently of a chosen presentation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {R S B C D E : Type u}
  [CommRing R] [CommRing S] [CommRing B] [CommRing C] [CommRing D] [CommRing E]
  [Algebra R S] [Algebra R B] [Algebra R C] [Algebra R D] [Algebra R E]

/-- Scalar extension of an algebra map, with the new base fixed. -/
abbrev affineScalarExtensionHom (f : B →ₐ[R] C) : S ⊗[R] B →ₐ[S] S ⊗[R] C :=
  Algebra.TensorProduct.map (AlgHom.id S S) f

/-- Scalar extension retains composition of the chosen maps. -/
@[simp]
theorem affineScalarExtensionHom_comp (f : B →ₐ[R] C) (g : C →ₐ[R] D) :
    affineScalarExtensionHom (S := S) (g.comp f) =
      (affineScalarExtensionHom (S := S) g).comp (affineScalarExtensionHom (S := S) f) := by
  apply Algebra.TensorProduct.ext_ring
  ext b
  rfl

/-- Each scalar-extended arrow forms a pullback with its original arrow. -/
theorem affineScalarExtensionHom_isPullback (f : B →ₐ[R] C) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[R] S ⊗[R] C).toRingHom))
      (Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := S) f).toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom)) := by
  have hf : Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact f.commutes a
  have hF : Spec.map (CommRingCat.ofHom
        (affineScalarExtensionHom (S := S) f).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] B))) =
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] C))) := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact (affineScalarExtensionHom (S := S) f).commutes a
  apply IsPullback.of_bot (t := integerModel_isPullback (AlgEquiv.refl :
    S ⊗[R] B ≃ₐ[S] S ⊗[R] B))
  · rw [hf, hF]
    simpa using integerModel_isPullback (AlgEquiv.refl :
      S ⊗[R] C ≃ₐ[S] S ⊗[R] C)
  · rw [← Spec.map_comp, ← Spec.map_comp]
    rfl

/-- Tensor scalar extension preserves an affine pullback with its actual maps. -/
theorem affineScalarExtensionHom_preserves_pullback
    (f : B →ₐ[R] C) (g : B →ₐ[R] D) (i : C →ₐ[R] E) (j : D →ₐ[R] E)
    (hp : IsPullback (Spec.map (CommRingCat.ofHom i.toRingHom))
      (Spec.map (CommRingCat.ofHom j.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom))) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := S) i).toRingHom))
      (Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := S) j).toRingHom))
      (Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := S) f).toRingHom))
      (Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := S) g).toRingHom)) := by
  have hAlg : i.comp f = j.comp g := by
    have hh := hp.w
    rw [← Spec.map_comp, ← Spec.map_comp] at hh
    exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective hh))
  have hcomm :
      Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := S) i).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := S) f).toRingHom) =
      Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := S) j).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := S) g).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b => exact congrArg (fun y ↦ a ⊗ₜ[R] y) (AlgHom.congr_fun hAlg b)
    | add x y hx hy => simp_all
  have ht := (affineScalarExtensionHom_isPullback (S := S) j).paste_horiz hp
  rw [(affineScalarExtensionHom_isPullback (S := S) i).w,
    (affineScalarExtensionHom_isPullback (S := S) g).w] at ht
  exact ht.of_right hcomm (affineScalarExtensionHom_isPullback (S := S) f)

end FLT.Mazur.Approximation
