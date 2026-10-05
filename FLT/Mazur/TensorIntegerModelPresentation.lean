/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorIntegerModelRecovery
public import FLT.Mazur.EnlargedPresentationModel

/-!
# Compatible presentations of products of affine coefficient models

Choose a finite presentation of the tensor product at the original stage,
then extend it using the prescribed recovery equivalence. This ensures that
the product presentation has the original coefficients and models the actual
product at every later stage.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] {n m r t : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin m))
  (Q : Algebra.Presentation A C (Fin r) (Fin t))
  (A₀ : Subalgebra ℤ A) [P.HasCoeffs A₀] [Q.HasCoeffs A₀]

/-- Products of finite presentation models remain finitely presented. -/
instance tensorIntegerModel_finitePresentation :
    Algebra.FinitePresentation A₀
      (P.ModelOfHasCoeffs A₀ ⊗[A₀] Q.ModelOfHasCoeffs A₀) := by
  let T := Algebra.Presentation.ofFinitePresentation A₀ (Q.ModelOfHasCoeffs A₀)
  let := (T.baseChange (P.ModelOfHasCoeffs A₀)).finitePresentation_of_isFinite
  exact Algebra.FinitePresentation.trans A₀ (P.ModelOfHasCoeffs A₀) _

/-- A finite presentation of the actual product of the old coefficient models. -/
abbrev tensorIntegerModelPresentation :=
  Algebra.Presentation.ofFinitePresentation A₀
    (P.ModelOfHasCoeffs A₀ ⊗[A₀] Q.ModelOfHasCoeffs A₀)

/-- A presentation of the original product chosen compatibly with the old stage. -/
abbrev tensorIntegerPresentation :=
  integerBaseChangedPresentation A₀ (tensorIntegerModelPresentation P Q A₀)
    (tensorIntegerModelRecoveryEquiv P Q A₀)

/-- The compatible presentation has the required coefficients at the old stage. -/
instance tensorIntegerPresentation_hasCoeffs :
    (tensorIntegerPresentation P Q A₀).HasCoeffs A₀ := inferInstance

/-- Identify its coefficient model with the tensor product of the given models. -/
def tensorIntegerPresentationEquiv :
    (tensorIntegerPresentation P Q A₀).ModelOfHasCoeffs A₀ ≃ₐ[A₀]
      P.ModelOfHasCoeffs A₀ ⊗[A₀] Q.ModelOfHasCoeffs A₀ :=
  integerBaseChangedModelEquiv A₀ (tensorIntegerModelPresentation P Q A₀)
    (tensorIntegerModelRecoveryEquiv P Q A₀)

/-- The identification preserves the original product recovery. -/
theorem tensorIntegerPresentationEquiv_recovery
    (b : (tensorIntegerPresentation P Q A₀).ModelOfHasCoeffs A₀) :
    (tensorIntegerPresentation P Q A₀).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b) =
      tensorIntegerModelRecoveryEquiv P Q A₀ (1 ⊗ₜ tensorIntegerPresentationEquiv P Q A₀ b) :=
  integerBaseChangedModelEquiv_recovery A₀ (tensorIntegerModelPresentation P Q A₀)
    (tensorIntegerModelRecoveryEquiv P Q A₀) b

end FLT.Mazur.Approximation
