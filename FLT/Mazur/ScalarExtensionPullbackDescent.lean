/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackCorner
public import FLT.Mazur.AffineSquareTensorComparison
public import FLT.Mazur.ScalarExtensionIsomorphismDescent

/-!
# Descending cartesian affine squares

A commutative square of finitely presented coefficient algebras which is
cartesian after recovery becomes cartesian at a finite coefficient stage.
The tensor comparison is constructed from the given arrows and its
bijectivity descends; a pullback at the initial stage is not assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- A recovered affine pullback descends with all four scalar-extended maps. -/
theorem exists_integer_scalarExtension_pullback {A : Type u} [CommRing A]
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    {R B C D : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A₀ R] [Algebra A₀ B] [Algebra A₀ C] [Algebra A₀ D]
    [Algebra.FinitePresentation A₀ R] [Algebra.FinitePresentation A₀ B]
    [Algebra.FinitePresentation A₀ C] [Algebra.FinitePresentation A₀ D]
    (f : R →ₐ[A₀] B) (g : R →ₐ[A₀] C)
    (i : B →ₐ[A₀] D) (j : C →ₐ[A₀] D) (hcomm : i.comp f = j.comp g)
    (hp : IsPullback
      (Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := A) i).toRingHom))
      (Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := A) j).toRingHom))
      (Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := A) f).toRingHom))
      (Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := A) g).toRingHom)))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
        IsPullback
          (Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := S) i).toRingHom))
          (Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := S) j).toRingHom))
          (Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := S) f).toRingHom))
          (Spec.map (CommRingCat.ofHom (affineScalarExtensionHom (S := S) g).toRingHom)) := by
  let := f.toRingHom.toAlgebra
  let := g.toRingHom.toAlgebra
  let : Algebra.FinitePresentation R C :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A₀ R C
  let : Algebra.FinitePresentation A₀ (B ⊗[R] C) :=
    Algebra.FinitePresentation.trans A₀ B (B ⊗[R] C)
  let l : B →ₐ[A₀] B ⊗[R] C :=
    (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] C).restrictScalars A₀
  let r : C →ₐ[A₀] B ⊗[R] C :=
    (Algebra.TensorProduct.includeRight : C →ₐ[R] B ⊗[R] C).restrictScalars A₀
  let q := affineSquareTensorComparison f g i j hcomm
  have hl : q.comp l = i := by ext b; exact affineSquareTensorComparison_left f g i j hcomm b
  have hr : q.comp r = j := by ext c; exact affineSquareTensorComparison_right f g i j hcomm c
  have ht : IsPullback (Spec.map (CommRingCat.ofHom l.toRingHom))
      (Spec.map (CommRingCat.ofHom r.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R B C)
  have hq : Function.Bijective (affineScalarExtensionHom (S := A) q) := by
    apply affinePullback_corner_bijective
      (affineScalarExtensionHom (S := A) f) (affineScalarExtensionHom (S := A) g)
      (affineScalarExtensionHom (S := A) l) (affineScalarExtensionHom (S := A) r)
      (affineScalarExtensionHom (S := A) i) (affineScalarExtensionHom (S := A) j)
      (affineScalarExtensionHom (S := A) q)
    · rw [← affineScalarExtensionHom_comp, hl]
    · rw [← affineScalarExtensionHom_comp, hr]
    · exact affineScalarExtensionHom_preserves_pullback f g l r ht
    · exact hp
  obtain ⟨S, hS, hsS, h, hqS⟩ := exists_integer_scalarExtension_bijective A₀ q hq s hs
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  refine ⟨S, hS, hsS, h, ?_⟩
  apply affinePullback_of_corner_bijective
    (affineScalarExtensionHom (S := S) f) (affineScalarExtensionHom (S := S) g)
    (affineScalarExtensionHom (S := S) l) (affineScalarExtensionHom (S := S) r)
    (affineScalarExtensionHom (S := S) i) (affineScalarExtensionHom (S := S) j)
    (affineScalarExtensionHom (S := S) q)
  · rw [← affineScalarExtensionHom_comp, hl]
  · rw [← affineScalarExtensionHom_comp, hr]
  · exact affineScalarExtensionHom_preserves_pullback f g l r ht
  · exact hqS

end FLT.Mazur.Approximation
