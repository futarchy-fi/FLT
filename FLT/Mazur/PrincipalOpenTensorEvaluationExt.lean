/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTensor

/-!
# Original localized functions determine a tensor-boundary evaluation

Maps over the extended coefficient ring are determined by their restriction
to the original integral localized algebra. This keeps the tensor operations
out of subsequent coordinate proofs.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.PrincipalOpenTensor
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {A : Type*} [CommRing A] [Algebra R A] (x : A)
  {B : Type*} [CommRing B] [Algebra S B]

/-- Evaluation on every original localized function determines the full scalar extension. -/
theorem evaluation_ext
    (f g : Localization.Away ((1 : S) ⊗ₜ[R] x) →ₐ[S] B)
    (h : ∀ z, f (coefficient S x z) = g (coefficient S x z)) : f = g := by
  apply AlgHom.ext
  intro z
  obtain ⟨z, rfl⟩ := (equiv S x).surjective z
  induction z using TensorProduct.inductionOn with
  | tmul s z => rw [equiv_tmul, map_smul, map_smul, h]
  | add z w hz hw => simp only [map_add, hz, hw]

end FLT.Mazur.PrincipalOpenTensor
