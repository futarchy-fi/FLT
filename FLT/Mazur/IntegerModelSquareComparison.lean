/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSquareScalarExtension
public import FLT.Mazur.IntegerModelBaseChange
public import FLT.Mazur.IntegerModelHomTransport

/-!
# Scalar-extension comparisons for model diagrams

Recovery and coefficient enlargement identify scalar-extended arrows with
the original and transported arrows respectively, as equalities of full
algebra maps.
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
  {A₀ : Subalgebra ℤ A} [P.HasCoeffs A₀] [Q.HasCoeffs A₀]
  (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)

/-- The full scalar-extended map recovers the original arrow. -/
theorem integerModelScalarExtension_recovery_hom (φ : B →ₐ[A] C)
    (hf : ∀ b, Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      φ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b))) :
    (Q.tensorModelOfHasCoeffsEquiv A₀).toAlgHom.comp
        (affineScalarExtensionHom (S := A) f) =
      φ.comp (P.tensorModelOfHasCoeffsEquiv A₀).toAlgHom := by
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.ext
  exact hf

/-- The model base-change equivalences identify the full transported arrow. -/
theorem integerModelScalarExtension_transport_hom
    {A₁ : Subalgebra ℤ A} [P.HasCoeffs A₁] [Q.HasCoeffs A₁] (h : A₀ ≤ A₁) :
    letI := (Subalgebra.inclusion h).toRingHom.toAlgebra
    (integerModelBaseChangeEquiv Q h).toAlgHom.comp
        (affineScalarExtensionHom (S := A₁) f) =
      (integerModelTransportHom P Q h f).comp
        (integerModelBaseChangeEquiv P h).toAlgHom := by
  let := (Subalgebra.inclusion h).toRingHom.toAlgebra
  apply Algebra.TensorProduct.ext_ring
  ext b
  change integerModelBaseChangeEquiv Q h (1 ⊗ₜ f b) =
    integerModelTransportHom P Q h f (integerModelBaseChangeEquiv P h (1 ⊗ₜ b))
  rw [integerModelBaseChangeEquiv_one_tmul, integerModelBaseChangeEquiv_one_tmul,
    integerModelTransportHom_transition]

end FLT.Mazur.Approximation
