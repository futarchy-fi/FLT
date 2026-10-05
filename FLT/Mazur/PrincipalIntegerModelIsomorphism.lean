/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelIsomorphismDescent
public import FLT.Mazur.PrincipalPresentationIntegerModel

/-!
# Eventual isomorphisms from canonical principal localizations

A comparison out of an old principal localization which recovers its
canonical scalar-extension identification becomes an isomorphism after
coefficient enlargement. The source is the canonical localization of the
enlarged model, and all old comparison values are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

set_option maxHeartbeats 800000 in
-- Comparing two independently constructed presentations requires extra elaboration.
/-- A recovered principal-localization comparison is eventually an isomorphism
of the canonical localization, compatible with every old localized element. -/
theorem exists_integer_model_principal_isomorphism {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
    (A₀ : Subalgebra ℤ A) [Algebra.FiniteType ℤ A₀] [P.HasCoeffs A₀]
    (x : P.ModelOfHasCoeffs A₀)
    (Q : Algebra.Presentation A
      (Localization.Away (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x))) (Fin r) (Fin t))
    [Q.HasCoeffs A₀]
    (F : Localization.Away x →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (hF : ∀ c, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ F c) =
      principalIntegerModelEquiv (P.tensorModelOfHasCoeffsEquiv A₀) x (1 ⊗ₜ c))
    (s : Set A) (hs : s.Finite) :
    ∃ A₁ : Subalgebra ℤ A, Algebra.FiniteType ℤ A₁ ∧ s ⊆ A₁ ∧
      ∃ h : A₀ ≤ A₁, ∃ _hP : P.HasCoeffs A₁, ∃ _hQ : Q.HasCoeffs A₁,
        ∃ e₁ : Localization.Away (integerModelTransition P h x) ≃ₐ[A₁]
            Q.ModelOfHasCoeffs A₁,
          letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
          ∀ c, e₁ (integerPrincipalBaseChangeEquiv P h x (1 ⊗ₜ c)) =
            integerModelTransition Q h (F c) := by
  let Q₀ := Algebra.Presentation.ofFinitePresentation A₀ (Localization.Away x)
  let e₀ := principalIntegerModelEquiv (P.tensorModelOfHasCoeffsEquiv A₀) x
  let R := integerBaseChangedPresentation A₀ Q₀ e₀
  let d := integerBaseChangedModelEquiv A₀ Q₀ e₀
  let f := F.comp d.toAlgHom
  have hf (b) : Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      (AlgEquiv.refl (R := A)) (R.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)) := by
    change Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ F (d b)) =
      R.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)
    rw [hF]
    exact (integerBaseChangedModelEquiv_recovery A₀ Q₀ e₀ b).symm
  obtain ⟨A₁, hA₁, hs₁, h, hR₁, hQ₁, e₁, he₁, _⟩ :=
    exists_integer_model_isomorphism R Q A₀ f (AlgEquiv.refl (R := A)) hf s hs
  let := hR₁
  let := hQ₁
  let : P.HasCoeffs A₁ := integerModel_hasCoeffs_mono P h
  let d₁ := integerPrincipalPresentationEquiv P x Q₀ h
  refine ⟨A₁, hA₁, hs₁, h, inferInstance, hQ₁, d₁.symm.trans e₁, ?_⟩
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  intro c
  change e₁ (d₁.symm (integerPrincipalBaseChangeEquiv P h x (1 ⊗ₜ c))) = _
  rw [integerPrincipalPresentationEquiv_symm_baseChange, he₁]
  change integerModelTransition Q h (F (d (d.symm c))) = _
  rw [AlgEquiv.apply_symm_apply]

end FLT.Mazur.Approximation
