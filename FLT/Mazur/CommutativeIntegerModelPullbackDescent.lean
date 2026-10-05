/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSquareEquivalences
public import FLT.Mazur.IntegerModelSquareComparison
public import FLT.Mazur.ScalarExtensionPullbackDescent

/-!
# Pullback descent for commutative model squares

A commutative square of fixed presentation models recovering a cartesian
square becomes cartesian after coefficient enlargement. All four arrows
are the specified transported maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- A commutative model square recovering an affine pullback becomes cartesian. -/
theorem exists_integer_model_pullback_of_commutative {A B C D E : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing E]
    [Algebra A B] [Algebra A C] [Algebra A D] [Algebra A E]
    {n m r t p q k l : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (R : Algebra.Presentation A D (Fin p) (Fin q))
    (T : Algebra.Presentation A E (Fin k) (Fin l))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀] [R.HasCoeffs A₀] [T.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (g : P.ModelOfHasCoeffs A₀ →ₐ[A₀] R.ModelOfHasCoeffs A₀)
    (i : Q.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)
    (j : R.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)
    (hcomm : i.comp f = j.comp g)
    (F : B →ₐ[A] C) (G : B →ₐ[A] D) (I : C →ₐ[A] E) (J : D →ₐ[A] E)
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      F (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (hg : ∀ b, R.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ g b) =
      G (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (hi : ∀ c, T.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ i c) =
      I (Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ c)))
    (hj : ∀ d, T.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ j d) =
      J (R.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ d)))
    (hp : IsPullback (Spec.map (CommRingCat.ofHom I.toRingHom))
      (Spec.map (CommRingCat.ofHom J.toRingHom))
      (Spec.map (CommRingCat.ofHom F.toRingHom))
      (Spec.map (CommRingCat.ofHom G.toRingHom))) (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S, ∃ _hQ : Q.HasCoeffs S,
        ∃ _hR : R.HasCoeffs S, ∃ _hT : T.HasCoeffs S,
          IsPullback
            (Spec.map (CommRingCat.ofHom (integerModelTransportHom Q T h i).toRingHom))
            (Spec.map (CommRingCat.ofHom (integerModelTransportHom R T h j).toRingHom))
            (Spec.map (CommRingCat.ofHom (integerModelTransportHom P Q h f).toRingHom))
            (Spec.map (CommRingCat.ofHom (integerModelTransportHom P R h g).toRingHom)) := by
  have hpA := (affineSquare_isPullback_iff_of_equivs
    (affineScalarExtensionHom (S := A) f) (affineScalarExtensionHom (S := A) g)
    (affineScalarExtensionHom (S := A) i) (affineScalarExtensionHom (S := A) j)
    F G I J (P.tensorModelOfHasCoeffsEquiv A₀) (Q.tensorModelOfHasCoeffsEquiv A₀)
    (R.tensorModelOfHasCoeffsEquiv A₀) (T.tensorModelOfHasCoeffsEquiv A₀)
    (integerModelScalarExtension_recovery_hom P Q f F hf)
    (integerModelScalarExtension_recovery_hom P R g G hg)
    (integerModelScalarExtension_recovery_hom Q T i I hi)
    (integerModelScalarExtension_recovery_hom R T j J hj)).mpr hp
  obtain ⟨S, hS, hsS, h, hpS⟩ :=
    exists_integer_scalarExtension_pullback A₀ f g i j hcomm hpA s hs
  let hP := integerModel_hasCoeffs_mono P h
  let hQ := integerModel_hasCoeffs_mono Q h
  let hR := integerModel_hasCoeffs_mono R h
  let hT := integerModel_hasCoeffs_mono T h
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  refine ⟨S, hS, hsS, h, hP, hQ, hR, hT, ?_⟩
  exact (affineSquare_isPullback_iff_of_equivs
    (affineScalarExtensionHom (S := S) f) (affineScalarExtensionHom (S := S) g)
    (affineScalarExtensionHom (S := S) i) (affineScalarExtensionHom (S := S) j)
    (integerModelTransportHom P Q h f) (integerModelTransportHom P R h g)
    (integerModelTransportHom Q T h i) (integerModelTransportHom R T h j)
    (integerModelBaseChangeEquiv P h) (integerModelBaseChangeEquiv Q h)
    (integerModelBaseChangeEquiv R h) (integerModelBaseChangeEquiv T h)
    (integerModelScalarExtension_transport_hom P Q f h)
    (integerModelScalarExtension_transport_hom P R g h)
    (integerModelScalarExtension_transport_hom Q T i h)
    (integerModelScalarExtension_transport_hom R T j h)).mp hpS

end FLT.Mazur.Approximation
