/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedIntegerChartComparison

/-!
# Transporting localized comparisons to larger coefficient stages

A localized equivalence retains its chart compatibility after any enlargement.
This allows independently descended restrictions to be put at a common stage.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- Localized chart equivalences persist under arbitrary coefficient enlargement. -/
theorem integerModel_localized_comparison_transport {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    {A₀ A₁ : Subalgebra ℤ A} [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    [P.HasCoeffs A₁] [Q.HasCoeffs A₁] (h : A₀ ≤ A₁)
    (x : P.ModelOfHasCoeffs A₀) (y : Q.ModelOfHasCoeffs A₀)
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (e : Localization.Away x ≃ₐ[A₀] Localization.Away y)
    (he : ∀ b, e (algebraMap _ (Localization.Away x) b) =
      algebraMap _ (Localization.Away y) (f b)) :
    ∃ e₁ : Localization.Away (integerModelTransition P h x) ≃ₐ[A₁]
        Localization.Away (integerModelTransition Q h y),
      ∀ b, e₁ (algebraMap _ (Localization.Away (integerModelTransition P h x)) b) =
        algebraMap _ (Localization.Away (integerModelTransition Q h y))
          (integerModelTransportHom P Q h f b) := by
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  let dP := integerPrincipalBaseChangeEquiv P h x
  let dQ := integerPrincipalBaseChangeEquiv Q h y
  let e₁ := (dP.symm.trans (Algebra.TensorProduct.congr (AlgEquiv.refl : A₁ ≃ₐ[A₁] A₁) e)).trans dQ
  refine ⟨e₁, ?_⟩
  let πP := IsScalarTower.toAlgHom A₁ (P.ModelOfHasCoeffs A₁)
    (Localization.Away (integerModelTransition P h x))
  let πQ := IsScalarTower.toAlgHom A₁ (Q.ModelOfHasCoeffs A₁)
    (Localization.Away (integerModelTransition Q h y))
  have hcomp : e₁.toAlgHom.comp πP =
      πQ.comp (integerModelTransportHom P Q h f) := by
    apply integerModel_hom_ext P h
    intro b
    change e₁ (algebraMap _ _ (integerModelTransition P h b)) =
      algebraMap _ _ (integerModelTransportHom P Q h f (integerModelTransition P h b))
    rw [integerModelTransportHom_transition]
    have hd (c : P.ModelOfHasCoeffs A₀) :
        dP (1 ⊗ₜ algebraMap _ (Localization.Away x) c) =
          algebraMap _ _ (integerModelTransition P h c) := by
      simp only [dP, integerPrincipalBaseChangeEquiv_tmul, map_one, one_mul]
    rw [← hd b]
    change dQ (Algebra.TensorProduct.congr (AlgEquiv.refl : A₁ ≃ₐ[A₁] A₁) e
      (dP.symm (dP (1 ⊗ₜ algebraMap _ (Localization.Away x) b)))) = _
    rw [AlgEquiv.symm_apply_apply]
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_toAlgHom, he, dQ,
      integerPrincipalBaseChangeEquiv_tmul, map_one, one_mul]
  exact fun b ↦ AlgHom.congr_fun hcomp b

end FLT.Mazur.Approximation
