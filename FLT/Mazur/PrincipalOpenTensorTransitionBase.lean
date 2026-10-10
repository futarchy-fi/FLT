/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTensorTransition

/-!
# Restricting tensor transitions to unlocalized functions

A localization equivalence compatible with an integral map preserves that
compatibility after tensor base change, on every function of the tensor algebra.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.PrincipalOpenTensor
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (x : A) (y : B) (e : Localization.Away x ≃ₐ[R] Localization.Away y)
  (f : A →ₐ[R] B)
  (hf : ∀ z, e (algebraMap A (Localization.Away x) z) =
    algebraMap B (Localization.Away y) (f z))

include hf

/-- The integral restriction square survives on all pure tensor functions. -/
theorem transition_tmul_base (s : S) (z : A) :
    transition S x y e
      (algebraMap (S ⊗[R] A) _ (s ⊗ₜ[R] z)) =
        algebraMap (S ⊗[R] B) _ (s ⊗ₜ[R] f z) := by
  rw [← equiv_tmul_base, equiv_tmul, map_smul, transition_coefficient, hf,
    ← equiv_tmul, equiv_tmul_base]

/-- The complete base restriction is the scalar extension of the original integral map. -/
theorem transition_base (z : S ⊗[R] A) :
    transition S x y e (algebraMap (S ⊗[R] A) _ z) =
      algebraMap (S ⊗[R] B) _
        (Algebra.TensorProduct.map (AlgHom.id S S) f z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s a =>
    rw [Algebra.TensorProduct.map_tmul]
    exact transition_tmul_base S x y e f hf s a
  | add a b ha hb => simp only [map_add, ha, hb]

end FLT.Mazur.PrincipalOpenTensor
