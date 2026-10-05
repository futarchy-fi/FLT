/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorIntegerModelPresentation

/-!
# Coordinate maps from products to overlaps

Two restriction maps into an overlap give its coordinate map from the
product. The compatible tensor presentation gives a map between fixed
presentation models, recovering the actual product map.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D] {n m r t k l : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin m))
  (Q : Algebra.Presentation A C (Fin r) (Fin t))
  (T : Algebra.Presentation A D (Fin k) (Fin l))
  (A₀ : Subalgebra ℤ A) [P.HasCoeffs A₀] [Q.HasCoeffs A₀] [T.HasCoeffs A₀]
  (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)
  (g : Q.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)

/-- The coordinate map of an overlap in the compatible product presentation. -/
def tensorIntegerModelMap :
    (tensorIntegerPresentation P Q A₀).ModelOfHasCoeffs A₀ →ₐ[A₀]
      T.ModelOfHasCoeffs A₀ :=
  (Algebra.TensorProduct.productMap f g).comp (tensorIntegerPresentationEquiv P Q A₀).toAlgHom

/-- The map from the product recovers the prescribed two restriction maps. -/
theorem tensorIntegerModelMap_recovery (φ : B →ₐ[A] D) (ψ : C →ₐ[A] D)
    (hf : ∀ b, T.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ f b) =
      φ (P.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ b)))
    (hg : ∀ c, T.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ g c) =
      ψ (Q.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ c)))
    (x : (tensorIntegerPresentation P Q A₀).ModelOfHasCoeffs A₀) :
    T.tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ tensorIntegerModelMap P Q T A₀ f g x) =
      Algebra.TensorProduct.productMap φ ψ
        ((tensorIntegerPresentation P Q A₀).tensorModelOfHasCoeffsEquiv A₀ (1 ⊗ₜ x)) := by
  rw [tensorIntegerPresentationEquiv_recovery]
  change integerModelRecoveryHom T
    (Algebra.TensorProduct.productMap f g (tensorIntegerPresentationEquiv P Q A₀ x)) = _
  generalize tensorIntegerPresentationEquiv P Q A₀ x = z
  induction z using TensorProduct.inductionOn with
  | tmul b c =>
    simp only [Algebra.TensorProduct.productMap_apply_tmul, map_mul,
      integerModelRecoveryHom_apply, hf, hg, tensorIntegerModelRecoveryEquiv_tmul]
  | add z w hz hw => simp_all [TensorProduct.tmul_add]

end FLT.Mazur.Approximation
