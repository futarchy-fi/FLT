/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution

/-!
# Tensor products of convolution functionals

Pairing two functionals on pure tensors commutes with convolution products
and powers. Precomposition by a coalgebra map also preserves powers.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open WithConv

namespace LinearMap

variable {R A B T : Type*} [CommRing R] [AddCommGroup A] [AddCommGroup B]
  [Module R A] [Module R B] [Coalgebra R A] [Coalgebra R B]
  [CommRing T] [Algebra R T]

/-- Pair convolution functionals by multiplying their values on pure tensors. -/
def convTensorPair (F : WithConv (A →ₗ[R] T)) (G : WithConv (B →ₗ[R] T)) :
    WithConv (A ⊗[R] B →ₗ[R] T) :=
  toConv ((Algebra.TensorProduct.lmul' R (S := T)).toLinearMap.comp
    (TensorProduct.map F.ofConv G.ofConv))

omit [Coalgebra R A] [Coalgebra R B] in
/-- The tensor pairing evaluates on pure tensors by multiplication. -/
@[simp] theorem convTensorPair_tmul (F : WithConv (A →ₗ[R] T))
    (G : WithConv (B →ₗ[R] T)) (a : A) (b : B) :
    convTensorPair F G (a ⊗ₜ[R] b) = F a * G b := rfl

/-- The tensor pairing preserves the pair of convolution units. -/
@[simp] theorem convTensorPair_one :
    convTensorPair (1 : WithConv (A →ₗ[R] T)) (1 : WithConv (B →ₗ[R] T)) = 1 := by
  apply WithConv.ext
  ext a b
  simp [mul_comm]

/-- Tensor pairing commutes with convolution products in both factors. -/
theorem convTensorPair_mul (F H : WithConv (A →ₗ[R] T))
    (G K : WithConv (B →ₗ[R] T)) :
    convTensorPair (F * H) (G * K) = convTensorPair F G * convTensorPair H K := by
  apply WithConv.ext
  dsimp only [convTensorPair, ofConv_toConv]
  have h := congrArg ofConv (TensorProduct.map_convMul_map
    (f := F) (h := H) (g := G) (k := K))
  simp only at h
  rw [← h]
  exact algHom_comp_convMul_distrib (Algebra.TensorProduct.lmul' R) _ _

/-- Tensor pairing commutes with equal convolution powers. -/
theorem convTensorPair_pow (F : WithConv (A →ₗ[R] T))
    (G : WithConv (B →ₗ[R] T)) (n : ℕ) :
    convTensorPair (F ^ n) (G ^ n) = convTensorPair F G ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, convTensorPair_mul, ih, pow_succ]

/-- Precomposition by a coalgebra map preserves the convolution unit. -/
theorem convOne_precomp_coalgHom (h : B →ₗc[R] A) :
    (1 : WithConv (A →ₗ[R] T)).ofConv.comp h.toLinearMap =
      (1 : WithConv (B →ₗ[R] T)).ofConv := by
  ext b
  simp

/-- Precomposition by a coalgebra map commutes with convolution powers. -/
theorem convPow_comp_coalgHom (F : WithConv (A →ₗ[R] T))
    (h : B →ₗc[R] A) (n : ℕ) :
    (F ^ n).ofConv.comp h.toLinearMap =
      (toConv (F.ofConv.comp h.toLinearMap) ^ n).ofConv := by
  induction n with
  | zero => exact convOne_precomp_coalgHom h
  | succ n ih =>
    rw [pow_succ, convMul_comp_coalgHom_distrib, ih]
    rfl

end LinearMap
