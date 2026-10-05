/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseChangedPresentationModel
public import FLT.Mazur.IntegerModelBaseChange

/-!
# Compatible presentation models at enlarged coefficient stages

A presentation induced from an old algebra models the scalar extension of
that algebra at every larger stage. Its comparison sends transitioned old
model elements to the corresponding pure tensors.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
  (A₀ : Subalgebra ℤ A) {C₀ : Type u} [CommRing C₀] [Algebra A₀ C₀]
  {n m : ℕ} (Q₀ : Algebra.Presentation A₀ C₀ (Fin n) (Fin m))
  (e : A ⊗[A₀] C₀ ≃ₐ[A] C)
  {A₁ : Subalgebra ℤ A}
  [(integerBaseChangedPresentation A₀ Q₀ e).HasCoeffs A₁] (h : A₀ ≤ A₁)

/-- Enlarged models of a compatible presentation identify with scalar extensions. -/
def integerBaseChangedModelEquivAt :
    letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
    (integerBaseChangedPresentation A₀ Q₀ e).ModelOfHasCoeffs A₁ ≃ₐ[A₁]
      A₁ ⊗[A₀] C₀ := by
  letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
  exact (integerModelBaseChangeEquiv (integerBaseChangedPresentation A₀ Q₀ e) h).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A₁ ≃ₐ[A₁] A₁)
      (integerBaseChangedModelEquiv A₀ Q₀ e))

/-- Old elements are sent to their pure tensors in the enlarged algebra. -/
@[simp]
theorem integerBaseChangedModelEquivAt_transition
    (b : (integerBaseChangedPresentation A₀ Q₀ e).ModelOfHasCoeffs A₀) :
    letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
    integerBaseChangedModelEquivAt A₀ Q₀ e h
      (integerModelTransition (integerBaseChangedPresentation A₀ Q₀ e) h b) =
        1 ⊗ₜ integerBaseChangedModelEquiv A₀ Q₀ e b := by
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  rw [← integerModelBaseChangeEquiv_one_tmul (integerBaseChangedPresentation A₀ Q₀ e) h]
  simp only [integerBaseChangedModelEquivAt, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]
  rfl

/-- Inverting the comparison on a pure tensor recovers the old transition map. -/
@[simp]
theorem integerBaseChangedModelEquivAt_symm_one_tmul (c : C₀) :
    letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
    (integerBaseChangedModelEquivAt A₀ Q₀ e h).symm (1 ⊗ₜ c) =
      integerModelTransition (integerBaseChangedPresentation A₀ Q₀ e) h
        ((integerBaseChangedModelEquiv A₀ Q₀ e).symm c) := by
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  apply (integerBaseChangedModelEquivAt A₀ Q₀ e h).injective
  simp

end FLT.Mazur.Approximation
