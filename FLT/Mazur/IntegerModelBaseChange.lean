/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelHomExtension

/-!
# Coefficient base change of a fixed presentation model

The transition between two coefficient models is a scalar extension, even
when the coefficient inclusion is not flat. The equivalence is constructed
from the unique extension property of model maps.
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
  {A₀ A₁ : Subalgebra ℤ A} [P.HasCoeffs A₀] [P.HasCoeffs A₁] (h : A₀ ≤ A₁)

/-- A larger coefficient model is the scalar extension of the old model. -/
def integerModelBaseChangeEquiv :
    letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
    A₁ ⊗[A₀] P.ModelOfHasCoeffs A₀ ≃ₐ[A₁] P.ModelOfHasCoeffs A₁ := by
  letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
  let f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] P.ModelOfHasCoeffs A₁ :=
    { integerModelTransition P h with
      commutes' := integerModelTransition_algebraMap P h }
  let F := Algebra.TensorProduct.lift (Algebra.ofId A₁ (P.ModelOfHasCoeffs A₁))
    f (fun _ _ ↦ .all _ _)
  let G := integerModelExtendHom P h
    (Algebra.TensorProduct.includeRight (R := A₀) (A := A₁)).toRingHom (by
      intro a
      exact Algebra.TensorProduct.includeRight.commutes a)
  have hFG : F.comp G = AlgHom.id A₁ _ := by
    apply integerModel_hom_ext P h
    intro b
    change F (G (integerModelTransition P h b)) = integerModelTransition P h b
    rw [integerModelExtendHom_transition]
    simp [F, f]
  have hGF : G.comp F = AlgHom.id A₁ _ := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext b
      change G (F (1 ⊗ₜ b)) = 1 ⊗ₜ b
      have hF : F (1 ⊗ₜ b) = integerModelTransition P h b := by simp [F, f]
      rw [hF, integerModelExtendHom_transition]
      rfl
  exact AlgEquiv.ofAlgHom F G hFG hGF

/-- The base change equivalence sends an old model element to its transition. -/
theorem integerModelBaseChangeEquiv_one_tmul (b : P.ModelOfHasCoeffs A₀) :
    letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
    integerModelBaseChangeEquiv P h (1 ⊗ₜ b) = integerModelTransition P h b := by
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  simp [integerModelBaseChangeEquiv, Algebra.TensorProduct.lift_tmul]

/-- Pure tensors recover the coefficient action on the transition map. -/
@[simp]
theorem integerModelBaseChangeEquiv_tmul (a : A₁) (b : P.ModelOfHasCoeffs A₀) :
    letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
    integerModelBaseChangeEquiv P h (a ⊗ₜ b) =
      algebraMap A₁ (P.ModelOfHasCoeffs A₁) a * integerModelTransition P h b := by
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  rfl

end FLT.Mazur.Approximation
