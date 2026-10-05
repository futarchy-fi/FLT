/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelBaseChange
public import FLT.Mazur.PrincipalOpenIntegerModel

/-!
# Principal localization and coefficient enlargement

Localizing an old model and then enlarging coefficients gives the canonical
localization of the enlarged model. The comparison retains the localization
map, including its values on every old model element.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {n m : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))
  {A₀ A₁ : Subalgebra ℤ A} [P.HasCoeffs A₀] [P.HasCoeffs A₁]
  (h : A₀ ≤ A₁) (x : P.ModelOfHasCoeffs A₀)

/-- Localization of a model commutes with enlargement of its coefficients. -/
def integerPrincipalBaseChangeEquiv :
    letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
    A₁ ⊗[A₀] Localization.Away x ≃ₐ[A₁]
      Localization.Away (integerModelTransition P h x) := by
  letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
  exact (IsLocalization.Away.tensorProductEquivTMulRight A₀ A₁ x
    (Localization.Away x)).trans
      (IsLocalization.algEquivOfAlgEquiv
        (M := Submonoid.powers ((1 : A₁) ⊗ₜ[A₀] x))
        (T := Submonoid.powers (integerModelTransition P h x))
        (Localization.Away ((1 : A₁) ⊗ₜ[A₀] x))
        (Localization.Away (integerModelTransition P h x))
        (integerModelBaseChangeEquiv P h) (by simp [Submonoid.map_powers]))

/-- The localization comparison commutes with scalar extension of the chart map. -/
@[simp]
theorem integerPrincipalBaseChangeEquiv_tmul (a : A₁) (b : P.ModelOfHasCoeffs A₀) :
    letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
    integerPrincipalBaseChangeEquiv P h x
      (a ⊗ₜ algebraMap _ (Localization.Away x) b) =
        algebraMap _ (Localization.Away (integerModelTransition P h x))
          (algebraMap A₁ _ a * integerModelTransition P h b) := by
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  simp only [integerPrincipalBaseChangeEquiv, AlgEquiv.trans_apply,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul,
    IsLocalization.algEquivOfAlgEquiv_eq, integerModelBaseChangeEquiv_tmul]

end FLT.Mazur.Approximation
