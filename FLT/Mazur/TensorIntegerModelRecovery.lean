/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelBaseChange
public import FLT.Mazur.IntegerModelHomTransport

/-!
# Tensor products of coefficient models

Scalar extension commutes with tensor products. Applied to two fixed
presentation models, this identifies the coordinate ring of their product
with the original product, and retains the recovery of pure tensors.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

/-- Scalar extension distributes over a tensor product of algebras. -/
def tensorScalarExtensionEquiv (R S B C : Type u)
    [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra R C] :
    S ⊗[R] (B ⊗[R] C) ≃ₐ[S] (S ⊗[R] B) ⊗[S] (S ⊗[R] C) :=
  (Algebra.TensorProduct.assoc R R S S B C).symm.trans
    (Algebra.TensorProduct.cancelBaseChange R S S (S ⊗[R] B) C).symm

/-- On pure tensors the first factor receives the scalar. -/
@[simp]
theorem tensorScalarExtensionEquiv_tmul (R S B C : Type u)
    [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] [Algebra R C] (a : S) (b : B) (c : C) :
    tensorScalarExtensionEquiv R S B C (a ⊗ₜ (b ⊗ₜ c)) =
      (a ⊗ₜ b) ⊗ₜ (1 ⊗ₜ c) := rfl

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] {n m r t : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin m))
  (Q : Algebra.Presentation A C (Fin r) (Fin t))
  (A₀ : Subalgebra ℤ A) [P.HasCoeffs A₀] [Q.HasCoeffs A₀]

/-- The tensor product of the two fixed models recovers the original product. -/
def tensorIntegerModelRecoveryEquiv :
    A ⊗[A₀] (P.ModelOfHasCoeffs A₀ ⊗[A₀] Q.ModelOfHasCoeffs A₀) ≃ₐ[A] B ⊗[A] C :=
  (tensorScalarExtensionEquiv A₀ A _ _).trans
    (Algebra.TensorProduct.congr (P.tensorModelOfHasCoeffsEquiv A₀)
      (Q.tensorModelOfHasCoeffsEquiv A₀))

/-- The product identification uses exactly the two prescribed recovery maps. -/
@[simp]
theorem tensorIntegerModelRecoveryEquiv_tmul
    (a : A) (b : P.ModelOfHasCoeffs A₀) (c : Q.ModelOfHasCoeffs A₀) :
    tensorIntegerModelRecoveryEquiv P Q A₀ (a ⊗ₜ (b ⊗ₜ c)) =
      P.tensorModelOfHasCoeffsEquiv A₀ (a ⊗ₜ b) ⊗ₜ
        Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ c) := rfl

end FLT.Mazur.Approximation
