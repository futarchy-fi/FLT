/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorIntegerModelMap

/-!
# Product coordinates after coefficient enlargement

The enlarged compatible tensor presentation is the actual tensor product
of the enlarged chart models. The transported overlap map is their product
map under this equivalence.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] {n m r t : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin m))
  (Q : Algebra.Presentation A C (Fin r) (Fin t))
  {A₀ A₁ : Subalgebra ℤ A} [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
  [P.HasCoeffs A₁] [Q.HasCoeffs A₁]
  [(tensorIntegerPresentation P Q A₀).HasCoeffs A₁] (h : A₀ ≤ A₁)

/-- The enlarged product presentation models the product of the enlarged charts. -/
def tensorIntegerPresentationEquivAt :
    (tensorIntegerPresentation P Q A₀).ModelOfHasCoeffs A₁ ≃ₐ[A₁]
      P.ModelOfHasCoeffs A₁ ⊗[A₁] Q.ModelOfHasCoeffs A₁ := by
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  exact (integerBaseChangedModelEquivAt A₀ (tensorIntegerModelPresentation P Q A₀)
    (tensorIntegerModelRecoveryEquiv P Q A₀) h).trans
    ((tensorScalarExtensionEquiv A₀ A₁ _ _).trans
      (Algebra.TensorProduct.congr (integerModelBaseChangeEquiv P h)
        (integerModelBaseChangeEquiv Q h)))

/-- Old pure tensors become pure tensors of the two transitioned chart elements. -/
@[simp]
theorem tensorIntegerPresentationEquivAt_transition_tmul
    (b : P.ModelOfHasCoeffs A₀) (c : Q.ModelOfHasCoeffs A₀) :
    tensorIntegerPresentationEquivAt P Q h
      (integerModelTransition (tensorIntegerPresentation P Q A₀) h
        ((tensorIntegerPresentationEquiv P Q A₀).symm (b ⊗ₜ c))) =
      integerModelTransition P h b ⊗ₜ integerModelTransition Q h c := by
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  simp only [tensorIntegerPresentationEquivAt, AlgEquiv.trans_apply,
    integerBaseChangedModelEquivAt_transition]
  change Algebra.TensorProduct.congr (integerModelBaseChangeEquiv P h)
    (integerModelBaseChangeEquiv Q h)
      (tensorScalarExtensionEquiv A₀ A₁ _ _
        (1 ⊗ₜ tensorIntegerPresentationEquiv P Q A₀
          ((tensorIntegerPresentationEquiv P Q A₀).symm (b ⊗ₜ c)))) = _
  simp

/-- Transport of the overlap coordinate map agrees with the actual enlarged product map. -/
theorem tensorIntegerModelMap_transport {D : Type u} [CommRing D] [Algebra A D]
    {k l : ℕ} (T : Algebra.Presentation A D (Fin k) (Fin l))
    [T.HasCoeffs A₀] [T.HasCoeffs A₁]
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)
    (g : Q.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀) :
    integerModelTransportHom (tensorIntegerPresentation P Q A₀) T h
      (tensorIntegerModelMap P Q T A₀ f g) =
      (Algebra.TensorProduct.productMap (integerModelTransportHom P T h f)
        (integerModelTransportHom Q T h g)).comp
          (tensorIntegerPresentationEquivAt P Q h).toAlgHom := by
  apply integerModel_hom_ext (tensorIntegerPresentation P Q A₀) h
  intro x
  obtain ⟨z, rfl⟩ := (tensorIntegerPresentationEquiv P Q A₀).symm.surjective x
  induction z using TensorProduct.inductionOn with
  | tmul b c =>
    simp only [integerModelTransportHom_transition, tensorIntegerModelMap,
      AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply, Algebra.TensorProduct.productMap_apply_tmul,
      map_mul, tensorIntegerPresentationEquivAt_transition_tmul]
  | add z w hz hw => simp_all

end FLT.Mazur.Approximation
