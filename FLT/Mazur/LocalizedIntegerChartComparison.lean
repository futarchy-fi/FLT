/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedIntegerModelIsomorphism
public import FLT.Mazur.PrincipalChartOpenImmersion

/-!
# Descended localized comparisons retain their chart maps

Compatibility on the old model determines compatibility on the whole
enlarged model. Consequently a descended localized comparison certifies
that the actual composite chart map is an open immersion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- A descended localized isomorphism retains the entire transported chart map. -/
theorem exists_integer_model_localized_chart_comparison {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (x : P.ModelOfHasCoeffs A₀) (y : Q.ModelOfHasCoeffs A₀)
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (F : Localization.Away x →ₐ[A₀] Localization.Away y)
    (hchart : ∀ b, F (algebraMap _ (Localization.Away x) b) =
      algebraMap _ (Localization.Away y) (f b))
    (e : Localization.Away (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x)) ≃ₐ[A]
      Localization.Away (Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ y)))
    (hF : ∀ c, principalIntegerModelEquiv (Q.tensorModelOfHasCoeffsEquiv A₀) y
        (1 ⊗ₜ F c) =
      e (principalIntegerModelEquiv (P.tensorModelOfHasCoeffsEquiv A₀) x (1 ⊗ₜ c)))
    (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ h : A₀ ≤ A₁, ∃ _hP : P.HasCoeffs A₁, ∃ _hQ : Q.HasCoeffs A₁,
        ∃ e₁ : Localization.Away (integerModelTransition P h x) ≃ₐ[A₁]
          Localization.Away (integerModelTransition Q h y),
          ∀ b, e₁ (algebraMap _ (Localization.Away (integerModelTransition P h x)) b) =
            algebraMap _ (Localization.Away (integerModelTransition Q h y))
              (integerModelTransportHom P Q h f b) := by
  obtain ⟨A₁, hA₁, hs₁, h, hP, hQ, e₁, he₁⟩ :=
    exists_integer_model_localized_isomorphism P Q A₀ x y F e hF s hs
  let := hP
  let := hQ
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
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
    simpa only [hchart, integerPrincipalBaseChangeEquiv_tmul, map_one, one_mul] using
      he₁ (algebraMap _ (Localization.Away x) b)
  exact ⟨A₁, hA₁, hs₁, h, hP, hQ, e₁, fun b ↦ AlgHom.congr_fun hcomp b⟩

/-- A localization comparison certifies the actual composite principal chart. -/
theorem localizedComparison_chart_isOpenImmersion {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S) (x : R) (y : S)
    (e : Localization.Away x ≃+* Localization.Away y)
    (he : ∀ b, e (algebraMap R (Localization.Away x) b) =
      algebraMap S (Localization.Away y) (f b)) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away y))) ≫
      Spec.map (CommRingCat.ofHom f)) := by
  rw [← Spec.map_comp]
  exact principalComparison_isOpenImmersion x
    ((algebraMap S (Localization.Away y)).comp f) e he

end FLT.Mazur.Approximation
