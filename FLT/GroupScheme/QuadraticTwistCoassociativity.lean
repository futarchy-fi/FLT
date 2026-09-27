/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.QuadraticTwistIdentities

/-!
# Coassociativity of quadratic descent

Tensor comparison respects maps and reassociation, so coassociativity descends
from the original Hopf algebra.
-/

@[expose] public section

open scoped TensorProduct

namespace QuadraticTwist

universe v
variable {R S A B C E : Type v}
variable [CommRing R] [CommRing S] [CommRing A] [CommRing B] [CommRing C] [CommRing E]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R E]

/-- Combining coefficients commutes with maps in either tensor factor. -/
theorem tensorBaseChange_map (f : A →ₐ[R] C) (g : B →ₐ[R] E)
    (x : S ⊗[R] A) (y : S ⊗[R] B) :
    tensorBaseChange R S C E
      (Algebra.TensorProduct.map (AlgHom.id R S) f x ⊗ₜ[S]
        Algebra.TensorProduct.map (AlgHom.id R S) g y) =
      Algebra.TensorProduct.map (AlgHom.id R S) (Algebra.TensorProduct.map f g)
        (tensorBaseChange R S A B (x ⊗ₜ[S] y)) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, TensorProduct.add_tmul, hx, hx']
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, TensorProduct.tmul_add, hy, hy']
    | tmul t b => rfl

/-- Combining three coefficients respects the tensor associator. -/
theorem tensorBaseChange_assoc (x : S ⊗[R] A) (y : S ⊗[R] B)
    (z : S ⊗[R] C) :
    tensorBaseChange R S A (B ⊗[R] C)
      (x ⊗ₜ[S] tensorBaseChange R S B C (y ⊗ₜ[S] z)) =
      Algebra.TensorProduct.map (AlgHom.id R S)
        (Algebra.TensorProduct.assoc R R R A B C).toAlgHom
        (tensorBaseChange R S (A ⊗[R] B) C
          (tensorBaseChange R S A B (x ⊗ₜ[S] y) ⊗ₜ[S] z)) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, TensorProduct.add_tmul, hx, hx']
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, TensorProduct.add_tmul,
        TensorProduct.tmul_add, hy, hy']
    | tmul t b =>
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' => simp only [map_add, TensorProduct.tmul_add, hz, hz']
      | tmul w c => simp [mul_assoc]

/-- Tensor products of involutions are involutions. -/
theorem tensor_involutive (ι : A ≃ₐ[R] A) (κ : B ≃ₐ[R] B)
    (hι : Function.Involutive ι) (hκ : Function.Involutive κ) :
    Function.Involutive (Algebra.TensorProduct.congr ι κ) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b => simp [hι a, hκ b]

end QuadraticTwist
