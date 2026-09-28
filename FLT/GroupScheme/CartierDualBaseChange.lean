/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualHopf
public import Mathlib.LinearAlgebra.Dual.BaseChange

/-!
# Base change of integral Cartier dual algebras

For finite free coordinate algebras, extension of scalars commutes with
the convolution dual. The comparison evaluates by the original integral
pairing followed by the scalar map.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Coalgebra

namespace HopfAlgebra.CartierDual

universe u

variable {R A : Type u} (S : Type u) [CommRing R] [CommRing A] [CommRing S]
  [Algebra R S] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

/-- The canonical linear comparison between the base change of a dual and
the dual of the base change. -/
def baseChangeLinearEquiv : S ⊗[R] CartierDual R A ≃ₗ[S] CartierDual S (S ⊗[R] A) :=
  (linearEquiv (R := R) (A := A)).baseChange R S _ _ ≪≫ₗ
    (TensorProduct.isBaseChange R A S).toDualBaseChange ≪≫ₗ
      (WithConv.linearEquiv S _).symm

/-- The comparison preserves the integral evaluation pairing. -/
@[simp] theorem baseChangeLinearEquiv_tmul (s : S) (φ : CartierDual R A) (a : A) :
    baseChangeLinearEquiv S (s ⊗ₜ φ) (1 ⊗ₜ a) = s * algebraMap R S (φ a) := by
  change (TensorProduct.isBaseChange R A S).toDualBaseChange
    (s ⊗ₜ φ.ofConv) (1 ⊗ₜ a) = _
  exact (TensorProduct.isBaseChange R A S).toDualBaseChange_tmul s φ.ofConv a

omit [Module.Finite R A] [Module.Free R A] in
private theorem baseChange_convMul_eval (φ ψ : CartierDual S (S ⊗[R] A)) (a : A) :
    (φ * ψ) (1 ⊗ₜ a) = ∑ i ∈ (ℛ R a).index,
      φ (1 ⊗ₜ (ℛ R a).left i) * ψ (1 ⊗ₜ (ℛ R a).right i) := by
  rw [LinearMap.convMul_apply, TensorProduct.comul_tmul, ← (ℛ R a).eq]
  simp [TensorProduct.tmul_sum]

variable [Coalgebra.IsCocomm R A]

omit [Coalgebra.IsCocomm R A] in
/-- The canonical base-change comparison is multiplicative for convolution. -/
theorem baseChangeLinearEquiv_mul (x y : S ⊗[R] CartierDual R A) :
    baseChangeLinearEquiv S (x * y) = baseChangeLinearEquiv S x * baseChangeLinearEquiv S y := by
  induction x using TensorProduct.inductionOn with
  | tmul s φ =>
    induction y using TensorProduct.inductionOn with
    | tmul t ψ =>
      apply WithConv.ext
      apply (TensorProduct.isBaseChange R A S).algHom_ext
      intro a
      change baseChangeLinearEquiv S ((s ⊗ₜ φ) * (t ⊗ₜ ψ)) (1 ⊗ₜ a) =
        (baseChangeLinearEquiv S (s ⊗ₜ φ) * baseChangeLinearEquiv S (t ⊗ₜ ψ)) (1 ⊗ₜ a)
      simp only [Algebra.TensorProduct.tmul_mul_tmul, baseChangeLinearEquiv_tmul,
        baseChange_convMul_eval, (ℛ R a).convMul_apply, map_sum, map_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    | add y z hy hz => simp [mul_add, hy, hz]
  | add x z hx hz => simp [add_mul, hx, hz]

/-- Cartier dual coordinate algebras commute with scalar extension for
finite free integral models. -/
def baseChangeAlgEquiv : S ⊗[R] CartierDual R A ≃ₐ[S] CartierDual S (S ⊗[R] A) :=
  { baseChangeLinearEquiv S with
    map_mul' := baseChangeLinearEquiv_mul S
    commutes' := by
      intro s
      apply WithConv.ext
      apply (TensorProduct.isBaseChange R A S).algHom_ext
      intro a
      change baseChangeLinearEquiv S (s ⊗ₜ (1 : CartierDual R A)) (1 ⊗ₜ a) = _
      simp [Algebra.smul_def, mul_comm] }

/-- The algebra comparison is the scalar extension of the integral pairing. -/
@[simp] theorem baseChangeAlgEquiv_tmul (s : S) (φ : CartierDual R A) (a : A) :
    baseChangeAlgEquiv S (s ⊗ₜ φ) (1 ⊗ₜ a) = s * algebraMap R S (φ a) :=
  baseChangeLinearEquiv_tmul S s φ a

end HopfAlgebra.CartierDual
