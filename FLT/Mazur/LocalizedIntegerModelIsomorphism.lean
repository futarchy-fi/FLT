/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelIsomorphismDescent
public import FLT.Mazur.PrincipalPresentationIntegerModel

/-!
# Descending comparisons between two canonical principal localizations

A map between localizations of fixed models which recovers an isomorphism
becomes an isomorphism after coefficient enlargement. Both ends remain the
canonical localizations of the enlarged models, with their old values retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
-- The two induced presentations and their localization identifications elaborate together.
/-- An isomorphism recovered by a map of canonical localizations descends to
canonical localizations at a larger coefficient stage. -/
theorem exists_integer_model_localized_isomorphism {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (Q : Algebra.Presentation A C (Fin r) (Fin t))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀]
    [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
    (x : P.ModelOfHasCoeffs A₀) (y : Q.ModelOfHasCoeffs A₀)
    (F : Localization.Away x →ₐ[A₀] Localization.Away y)
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
          letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
          ∀ c, e₁ (integerPrincipalBaseChangeEquiv P h x (1 ⊗ₜ c)) =
            integerPrincipalBaseChangeEquiv Q h y (1 ⊗ₜ F c) := by
  let P₀ := Algebra.Presentation.ofFinitePresentation A₀ (Localization.Away x)
  let Q₀ := Algebra.Presentation.ofFinitePresentation A₀ (Localization.Away y)
  let eP := principalIntegerModelEquiv (P.tensorModelOfHasCoeffsEquiv A₀) x
  let eQ := principalIntegerModelEquiv (Q.tensorModelOfHasCoeffsEquiv A₀) y
  let L := integerPrincipalPresentation P x P₀
  let M := integerPrincipalPresentation Q y Q₀
  let dP := integerBaseChangedModelEquiv A₀ P₀ eP
  let dQ := integerBaseChangedModelEquiv A₀ Q₀ eQ
  let f := dQ.symm.toAlgHom.comp (F.comp dP.toAlgHom)
  have hf (b) : M.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      e (L.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)) := by
    rw [integerBaseChangedModelEquiv_recovery, integerBaseChangedModelEquiv_recovery]
    change eQ (1 ⊗ₜ dQ (dQ.symm (F (dP b)))) = e (eP (1 ⊗ₜ dP b))
    rw [AlgEquiv.apply_symm_apply]
    exact hF (dP b)
  obtain ⟨A₁, hA₁, hs₁, h, hL, hM, e₁, he₁, _⟩ :=
    exists_integer_model_isomorphism L M A₀ f e hf s hs
  let := hL
  let := hM
  let : P.HasCoeffs A₁ := integerModel_hasCoeffs_mono P h
  let : Q.HasCoeffs A₁ := integerModel_hasCoeffs_mono Q h
  let dP₁ := integerPrincipalPresentationEquiv P x P₀ h
  let dQ₁ := integerPrincipalPresentationEquiv Q y Q₀ h
  refine ⟨A₁, hA₁, hs₁, h, inferInstance, inferInstance,
    (dP₁.symm.trans e₁).trans dQ₁, ?_⟩
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  intro c
  change dQ₁ (e₁ (dP₁.symm (integerPrincipalBaseChangeEquiv P h x (1 ⊗ₜ c)))) = _
  rw [integerPrincipalPresentationEquiv_symm_baseChange, he₁,
    integerPrincipalPresentationEquiv_transition]
  change integerPrincipalBaseChangeEquiv Q h y
    (1 ⊗ₜ dQ (dQ.symm (F (dP (dP.symm c))))) = _
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

end FLT.Mazur.Approximation
