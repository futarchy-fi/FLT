/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution

/-! # Multiplication and tensor squares of convolution powers -/

@[expose] public noncomputable section
open scoped TensorProduct
open WithConv
namespace HopfAlgebra
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Bialgebra R A] [Algebra R B]

/-- Precomposition by the original multiplication respects convolution powers. -/
theorem convPow_comp_mul (f : A →ₗ[R] B) (N : ℕ) :
    (toConv f ^ N).ofConv.comp (LinearMap.mul' R A) =
      (toConv (f.comp (LinearMap.mul' R A)) ^ N).ofConv := by
  induction N with
  | zero => ext a b; simp [LinearMap.convOne_apply, map_mul, mul_comm]
  | succ n ih =>
    rw [pow_succ]
    change (toConv f ^ n * toConv f).ofConv.comp
      (Bialgebra.mulCoalgHom R A).toLinearMap = _
    rw [LinearMap.convMul_comp_coalgHom_distrib]
    change (toConv ((toConv f ^ n).ofConv.comp (LinearMap.mul' R A)) *
      toConv (f.comp (LinearMap.mul' R A))).ofConv = _
    rw [ih]
    rfl

/-- The tensor square of a functional followed by actual target multiplication. -/
def convolutionTensorSquare (f : A →ₗ[R] B) : A ⊗[R] A →ₗ[R] B :=
  (Algebra.TensorProduct.lmul' R (S := B)).toLinearMap.comp (TensorProduct.map f f)

/-- Tensor squaring commutes with convolution multiplication. -/
theorem convolutionTensorSquare_mul (f g : WithConv (A →ₗ[R] B)) :
    convolutionTensorSquare (f * g).ofConv =
      (toConv (convolutionTensorSquare f.ofConv) *
        toConv (convolutionTensorSquare g.ofConv)).ofConv := by
  unfold convolutionTensorSquare
  rw [← LinearMap.algHom_comp_convMul_distrib, TensorProduct.map_convMul_map]

/-- Tensor squaring commutes with convolution powers. -/
theorem convolutionTensorSquare_pow (f : A →ₗ[R] B) (N : ℕ) :
    convolutionTensorSquare (toConv f ^ N).ofConv =
      (toConv (convolutionTensorSquare f) ^ N).ofConv := by
  induction N with
  | zero => ext a b; simp [convolutionTensorSquare, LinearMap.convOne_apply, map_mul, mul_comm]
  | succ n ih => rw [pow_succ, convolutionTensorSquare_mul, ih]; rfl

/-- Evaluation at the unit turns convolution powers into ordinary powers. -/
theorem convPow_apply_one (f : A →ₗ[R] B) (N : ℕ) :
    (toConv f ^ N) 1 = (f 1) ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LinearMap.convMul_apply, Bialgebra.comul_one]
    change (LinearMap.mul' R B)
      (TensorProduct.map (toConv f ^ n).ofConv f (1 ⊗ₜ[R] 1)) = _
    simp only [TensorProduct.map_tmul, LinearMap.mul'_apply, ih, pow_succ]

/-- Postcomposition by an algebra map preserves convolution powers of linear maps. -/
theorem algHom_comp_linear_convPow {C : Type*} [CommRing C] [Algebra R C]
    (q : B →ₐ[R] C) (f : A →ₗ[R] B) (N : ℕ) :
    q.toLinearMap.comp (toConv f ^ N).ofConv =
      (toConv (q.toLinearMap.comp f) ^ N).ofConv := by
  induction N with
  | zero => ext a; simp
  | succ n ih =>
    rw [pow_succ, LinearMap.algHom_comp_convMul_distrib, ih]
    rfl

/-- Precomposition by an actual bialgebra map preserves convolution powers. -/
theorem linear_convPow_comp_bialgHom {D : Type*} [CommRing D] [Bialgebra R D]
    (h : D →ₐc[R] A) (f : A →ₗ[R] B) (N : ℕ) :
    (toConv f ^ N).ofConv.comp h.toLinearMap =
      (toConv (f.comp h.toLinearMap) ^ N).ofConv := by
  induction N with
  | zero => ext a; simp
  | succ n ih =>
    rw [pow_succ]
    change (toConv f ^ n * toConv f).ofConv.comp h.toCoalgHom.toLinearMap = _
    rw [LinearMap.convMul_comp_coalgHom_distrib]
    change (toConv ((toConv f ^ n).ofConv.comp h.toLinearMap) *
      toConv (f.comp h.toLinearMap)).ofConv = _
    rw [ih]
    rfl

end HopfAlgebra
