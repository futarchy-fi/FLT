/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTensor
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The actual tensor base change of a principal-open transition

An integral overlap equivalence extends to the localizations of the actual
tensor algebras. Its square retains every integral localized function.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.PrincipalOpenTensor
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (x : A) (y : B) (e : Localization.Away x ≃ₐ[R] Localization.Away y)

/-- Extend the original overlap equivalence, retaining both original tensor localizations. -/
def transition : Localization.Away ((1 : S) ⊗ₜ[R] x) ≃ₐ[S]
    Localization.Away ((1 : S) ⊗ₜ[R] y) :=
  (equiv (R := R) S x).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e).trans (equiv (R := R) S y))

/-- The transition is the base change of the original integral overlap on all functions. -/
theorem transition_coefficient (a : Localization.Away x) :
    transition (R := R) S x y e (coefficient (R := R) S x a) = coefficient (R := R) S y (e a) := by
  change equiv (R := R) S y
        (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e
    ((equiv (R := R) S x).symm (equiv (R := R) S x ((1 : S) ⊗ₜ[R] a)))) =
      equiv (R := R) S y ((1 : S) ⊗ₜ[R] e a)
  rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  rfl

/-- The full tensor comparison square commutes before restricting to integral functions. -/
theorem transition_square (a : S ⊗[R] Localization.Away x) :
    transition (R := R) S x y e (equiv (R := R) S x a) =
      equiv (R := R) S y
        (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e a) := by
  simp only [transition, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

/-- The inverse comparison retains the reverse original overlap square. -/
theorem transition_symm_coefficient (b : Localization.Away y) :
    (transition (R := R) S x y e).symm (coefficient (R := R) S y b) =
      coefficient (R := R) S x (e.symm b) := by
  apply (transition (R := R) S x y e).injective
  rw [AlgEquiv.apply_symm_apply, transition_coefficient, AlgEquiv.apply_symm_apply]

end FLT.Mazur.PrincipalOpenTensor
