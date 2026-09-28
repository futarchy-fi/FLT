/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualCoalgebra

/-!
# The integral Cartier dual Hopf algebra

The convolution algebra and the transpose coalgebra of a finite projective
commutative, cocommutative Hopf algebra are compatible. Transposing the
antipode gives the antipode of the integral dual.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Coalgebra

namespace HopfAlgebra.CartierDual

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [Module.Finite R A] [Module.Projective R A] [Coalgebra.IsCocomm R A]

omit [Coalgebra.IsCocomm R A] in
private theorem tensor_mul_eval (t s : CartierDual R A ⊗[R] CartierDual R A) (a b : A) :
    tensorEquiv R A A (t * s) (a ⊗ₜ b) =
      ∑ i ∈ (ℛ R a).index, ∑ j ∈ (ℛ R b).index,
        tensorEquiv R A A t ((ℛ R a).left i ⊗ₜ (ℛ R b).left j) *
          tensorEquiv R A A s ((ℛ R a).right i ⊗ₜ (ℛ R b).right j) := by
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ =>
    induction s using TensorProduct.inductionOn with
    | tmul χ ω =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorEquiv_tmul,
        (ℛ R a).convMul_apply, (ℛ R b).convMul_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    | add x y hx hy =>
      simp [mul_add, hx, hy, Finset.sum_add_distrib]
  | add x y hx hy =>
    simp [add_mul, hx, hy, Finset.sum_add_distrib]

/-- The transpose comultiplication preserves convolution products. -/
theorem comul_mul (φ ψ : CartierDual R A) : comul (φ * ψ) = comul φ * comul ψ := by
  apply tensor_ext R A A
  intro a b
  rw [comul_eval, tensor_mul_eval]
  simpa [Finset.sum_product] using ((ℛ R a).mul (ℛ R b)).convMul_apply φ ψ

/-- The convolution algebra and transpose coalgebra form a bialgebra. -/
instance instBialgebra : Bialgebra R (CartierDual R A) :=
  Bialgebra.mk' R (CartierDual R A)
    (by change (1 : CartierDual R A) 1 = 1; simp)
    (by
      intro φ ψ
      change (φ * ψ) 1 = φ 1 * ψ 1
      simp [Algebra.TensorProduct.one_def])
    (by
      apply tensor_ext R A A
      intro a b
      change tensorEquiv R A A (comul 1) (a ⊗ₜ b) = _
      simp [Algebra.TensorProduct.one_def])
    (by exact comul_mul _ _)

/-- The antipode of the integral dual is precomposition with the original antipode. -/
def antipode : CartierDual R A →ₗ[R] CartierDual R A :=
  linearEquiv.symm.toLinearMap ∘ₗ (HopfAlgebra.antipode R).dualMap ∘ₗ
    linearEquiv.toLinearMap

omit [Module.Finite R A] [Module.Projective R A] [Coalgebra.IsCocomm R A] in
/-- Evaluation of the transposed antipode. -/
@[simp] theorem antipode_apply (φ : CartierDual R A) (a : A) :
    antipode φ a = φ (HopfAlgebra.antipode R a) := rfl

omit [Coalgebra.IsCocomm R A] in
private theorem antipode_left_eval (t : CartierDual R A ⊗[R] CartierDual R A) (a : A) :
    (LinearMap.mul' R (CartierDual R A) (antipode.rTensor _ t)) a =
      ∑ i ∈ (ℛ R a).index,
        tensorEquiv R A A t (HopfAlgebra.antipode R ((ℛ R a).left i) ⊗ₜ
          (ℛ R a).right i) := by
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ => simp [(ℛ R a).convMul_apply]
  | add x y hx hy => simp [hx, hy, Finset.sum_add_distrib]

omit [Coalgebra.IsCocomm R A] in
private theorem antipode_right_eval (t : CartierDual R A ⊗[R] CartierDual R A) (a : A) :
    (LinearMap.mul' R (CartierDual R A) (antipode.lTensor _ t)) a =
      ∑ i ∈ (ℛ R a).index,
        tensorEquiv R A A t ((ℛ R a).left i ⊗ₜ
          HopfAlgebra.antipode R ((ℛ R a).right i)) := by
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ => simp [(ℛ R a).convMul_apply]
  | add x y hx hy => simp [hx, hy, Finset.sum_add_distrib]

/-- The finite projective integral dual is a Hopf algebra. -/
instance instHopfAlgebra : HopfAlgebra R (CartierDual R A) where
  antipode := antipode
  mul_antipode_rTensor_comul := by
    ext φ : 1
    apply WithConv.ext
    ext a
    change (LinearMap.mul' R (CartierDual R A) (antipode.rTensor _ (comul φ))) a =
      algebraMap R (CartierDual R A) (φ 1) a
    rw [antipode_left_eval]
    simp only [comul_eval, ← map_sum]
    rw [HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit (ℛ R a)]
    simp [Algebra.algebraMap_eq_smul_one, mul_comm]
  mul_antipode_lTensor_comul := by
    ext φ : 1
    apply WithConv.ext
    ext a
    change (LinearMap.mul' R (CartierDual R A) (antipode.lTensor _ (comul φ))) a =
      algebraMap R (CartierDual R A) (φ 1) a
    rw [antipode_right_eval]
    simp only [comul_eval, ← map_sum]
    rw [HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit (ℛ R a)]
    simp [Algebra.algebraMap_eq_smul_one, mul_comm]

end HopfAlgebra.CartierDual
