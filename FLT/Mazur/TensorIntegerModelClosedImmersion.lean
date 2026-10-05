/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorIntegerModelTransport
public import FLT.Mazur.IntegerModelClosedImmersionDescent

/-!
# Descent of closed overlap maps into chart products

If the recovered overlap map into the product of two affine charts is a
closed immersion, the actual product of their enlarged coefficient models
has the same property. The conclusion concerns the original transported
restriction maps, rather than an independently chosen model of the product.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- A closed overlap in an affine product becomes closed at a larger coefficient stage. -/
theorem exists_tensor_integer_model_closedImmersion {A B C D : Type u}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] {n m r t k l : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (T : Algebra.Presentation A D (Fin k) (Fin l))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀] [T.HasCoeffs A₀]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)
    (g : Q.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)
    (φ : B →ₐ[A] D) (ψ : C →ₐ[A] D)
    [IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap φ ψ).toRingHom))]
    (hf : ∀ b, T.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      φ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (hg : ∀ c, T.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ g c) =
      ψ (Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ c)))
    (s : Set A) (hs : s.Finite) :
    ∃ S : Subalgebra ℤ A, Algebra.FiniteType ℤ S ∧ s ⊆ S ∧
      ∃ h : A₀ ≤ S, ∃ _hP : P.HasCoeffs S, ∃ _hQ : Q.HasCoeffs S,
        ∃ _hT : T.HasCoeffs S,
          IsClosedImmersion (Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.productMap (integerModelTransportHom P T h f)
              (integerModelTransportHom Q T h g)).toRingHom)) := by
  obtain ⟨S, hS, hsS, h, hPQ, hT, hc⟩ := exists_integer_model_closedImmersion
    (tensorIntegerPresentation P Q A₀) T A₀ (tensorIntegerModelMap P Q T A₀ f g)
    (Algebra.TensorProduct.productMap φ ψ)
    (tensorIntegerModelMap_recovery P Q T A₀ f g φ ψ hf hg) s hs
  let := hPQ
  let := hT
  let hP : P.HasCoeffs S := integerModel_hasCoeffs_mono P h
  let hQ : Q.HasCoeffs S := integerModel_hasCoeffs_mono Q h
  refine ⟨S, hS, hsS, h, hP, hQ, hT, ?_⟩
  rw [tensorIntegerModelMap_transport] at hc
  have he : CommRingCat.ofHom
      (((Algebra.TensorProduct.productMap (integerModelTransportHom P T h f)
        (integerModelTransportHom Q T h g)).comp
          (tensorIntegerPresentationEquivAt P Q h).toAlgHom).toRingHom) =
      CommRingCat.ofHom (tensorIntegerPresentationEquivAt P Q h).toRingHom ≫
        CommRingCat.ofHom (Algebra.TensorProduct.productMap
          (integerModelTransportHom P T h f) (integerModelTransportHom Q T h g)).toRingHom := rfl
  rw [he, Spec.map_comp] at hc
  let : IsIso (CommRingCat.ofHom (tensorIntegerPresentationEquivAt P Q h).toRingHom) :=
    (tensorIntegerPresentationEquivAt P Q h).toRingEquiv.toCommRingCatIso.isIso_hom
  exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ _).mp hc

end FLT.Mazur.Approximation
