/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EnlargedPresentationModel
public import FLT.Mazur.PrincipalModelBaseChange

/-!
# Compatible presentation models of principal localizations

Present the localization of an old model and extend that presentation to
the original base. At every enlarged coefficient stage its model is the
canonical localization of the enlarged source model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {n m r t : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
  {A₀ A₁ : Subalgebra ℤ A} [P.HasCoeffs A₀] [P.HasCoeffs A₁]
  (x : P.ModelOfHasCoeffs A₀)
  (Q₀ : Algebra.Presentation A₀ (Localization.Away x) (Fin r) (Fin t))

/-- The presentation induced from a presentation of the old principal localization. -/
abbrev integerPrincipalPresentation :=
  integerBaseChangedPresentation A₀ Q₀
    (principalIntegerModelEquiv (P.tensorModelOfHasCoeffsEquiv A₀) x)

variable [(integerPrincipalPresentation P x Q₀).HasCoeffs A₁] (h : A₀ ≤ A₁)

/-- The enlarged compatible model is the canonical principal localization. -/
def integerPrincipalPresentationEquiv :
    (integerPrincipalPresentation P x Q₀).ModelOfHasCoeffs A₁ ≃ₐ[A₁]
      Localization.Away (integerModelTransition P h x) := by
  letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
  exact (integerBaseChangedModelEquivAt A₀ Q₀
    (principalIntegerModelEquiv (P.tensorModelOfHasCoeffsEquiv A₀) x) h).trans
    (integerPrincipalBaseChangeEquiv P h x)

/-- The comparison retains the full old localization, not only its generators. -/
theorem integerPrincipalPresentationEquiv_transition
    (c : (integerPrincipalPresentation P x Q₀).ModelOfHasCoeffs A₀) :
    letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
    integerPrincipalPresentationEquiv P x Q₀ h
      (integerModelTransition (integerPrincipalPresentation P x Q₀) h c) =
      integerPrincipalBaseChangeEquiv P h x
        (1 ⊗ₜ integerBaseChangedModelEquiv A₀ Q₀
          (principalIntegerModelEquiv (P.tensorModelOfHasCoeffsEquiv A₀) x) c) := by
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  simp [integerPrincipalPresentationEquiv]

/-- The inverse comparison on the old localization is its model transition. -/
theorem integerPrincipalPresentationEquiv_symm_baseChange (c : Localization.Away x) :
    letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
    (integerPrincipalPresentationEquiv P x Q₀ h).symm
      (integerPrincipalBaseChangeEquiv P h x (1 ⊗ₜ c)) =
        integerModelTransition (integerPrincipalPresentation P x Q₀) h
        ((integerBaseChangedModelEquiv A₀ Q₀
          (principalIntegerModelEquiv (P.tensorModelOfHasCoeffsEquiv A₀) x)).symm c) := by
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  apply (integerPrincipalPresentationEquiv P x Q₀ h).injective
  simp only [AlgEquiv.apply_symm_apply, integerPrincipalPresentationEquiv_transition]

/-- The inverse comparison preserves the old principal chart map. -/
@[simp]
theorem integerPrincipalPresentationEquiv_symm_chart (b : P.ModelOfHasCoeffs A₀) :
    (integerPrincipalPresentationEquiv P x Q₀ h).symm
      (algebraMap _ (Localization.Away (integerModelTransition P h x))
        (integerModelTransition P h b)) =
      integerModelTransition (integerPrincipalPresentation P x Q₀) h
        ((integerBaseChangedModelEquiv A₀ Q₀
          (principalIntegerModelEquiv (P.tensorModelOfHasCoeffsEquiv A₀) x)).symm
        (algebraMap _ (Localization.Away x) b)) := by
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  simpa using integerPrincipalPresentationEquiv_symm_baseChange P x Q₀ h
    (algebraMap _ (Localization.Away x) b)

end FLT.Mazur.Approximation
