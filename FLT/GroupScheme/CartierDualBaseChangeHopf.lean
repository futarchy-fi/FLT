/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualBaseChange

/-!
# Scalar extension respects the dual Hopf structure

The perfect tensor pairing tests the coalgebra compatibility of the
base-change comparison on integral generators.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Coalgebra

namespace HopfAlgebra.CartierDual

universe u

variable {R A : Type u} (S : Type u) [CommRing R] [CommRing A] [CommRing S]
  [Algebra R S] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

/-- The perfect pairing on tensors of scalar-extended integral duals. -/
def baseChangeTensorEquiv :
    (S ⊗[R] CartierDual R A) ⊗[S] (S ⊗[R] CartierDual R A) ≃ₗ[S]
      Module.Dual S ((S ⊗[R] A) ⊗[S] (S ⊗[R] A)) :=
  (TensorProduct.congr (baseChangeAlgEquiv (R := R) (A := A) S).toLinearEquiv
    (baseChangeAlgEquiv (R := R) (A := A) S).toLinearEquiv).trans
      (tensorEquiv S (S ⊗[R] A) (S ⊗[R] A))

/-- On pure tensors the perfect pairing is the product of evaluations. -/
@[simp] theorem baseChangeTensorEquiv_tmul (x y : S ⊗[R] CartierDual R A) (a b : A) :
    baseChangeTensorEquiv S (x ⊗ₜ y) ((1 ⊗ₜ a) ⊗ₜ[S] (1 ⊗ₜ b)) =
      baseChangeAlgEquiv S x (1 ⊗ₜ a) * baseChangeAlgEquiv S y (1 ⊗ₜ b) := by
  simp [baseChangeTensorEquiv]

/-- Integral evaluations separate tensors after scalar extension. -/
theorem baseChange_tensor_ext
    {x y : (S ⊗[R] CartierDual R A) ⊗[S] (S ⊗[R] CartierDual R A)}
    (h : ∀ a b, baseChangeTensorEquiv S x ((1 ⊗ₜ a) ⊗ₜ[S] (1 ⊗ₜ b)) =
      baseChangeTensorEquiv S y ((1 ⊗ₜ a) ⊗ₜ[S] (1 ⊗ₜ b))) : x = y := by
  apply (baseChangeTensorEquiv S).injective
  apply TensorProduct.ext'
  intro v w
  induction v using TensorProduct.inductionOn with
  | tmul s a =>
    induction w using TensorProduct.inductionOn with
    | tmul t b =>
      rw [show s ⊗ₜ[R] a = s • ((1 : S) ⊗ₜ[R] a) by
          simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        show t ⊗ₜ[R] b = t • ((1 : S) ⊗ₜ[R] b) by
          simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
        TensorProduct.smul_tmul_smul]
      simp only [map_smul, h]
    | add w z hw hz => simp [TensorProduct.tmul_add, hw, hz]
  | add v z hv hz => simp [TensorProduct.add_tmul, hv, hz]

private theorem sum_comul_eval (φ : CartierDual R A) (a b : A) :
    ∑ i ∈ (ℛ R φ).index, ((ℛ R φ).left i) a * ((ℛ R φ).right i) b = φ (a * b) := by
  have h := comul_eval φ a b
  change tensorEquiv R A A (Coalgebra.comul φ) (a ⊗ₜ b) = _ at h
  rw [← (ℛ R φ).eq] at h
  simpa using h

set_option synthInstance.maxHeartbeats 100000 in
-- The nested scalar and tensor products require extra instance synthesis.
/-- Comultiplication after scalar extension is transposed multiplication. -/
theorem baseChange_comul_eval (x : S ⊗[R] CartierDual R A) (a b : A) :
    baseChangeTensorEquiv S (Coalgebra.comul x) ((1 ⊗ₜ a) ⊗ₜ[S] (1 ⊗ₜ b)) =
      baseChangeAlgEquiv S x (1 ⊗ₜ (a * b)) := by
  induction x using TensorProduct.inductionOn with
  | tmul s φ =>
    rw [TensorProduct.comul_tmul, ← (ℛ R φ).eq]
    simp only [CommSemiring.comul_apply, TensorProduct.tmul_sum, map_sum,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, LinearMap.sum_apply,
      baseChangeTensorEquiv_tmul, baseChangeAlgEquiv_tmul, one_mul]
    rw [← sum_comul_eval φ a b]
    simp only [map_sum, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  | add x y hx hy => simp [hx, hy]

/-- The base-change comparison preserves the dual counit. -/
theorem baseChange_counit (x : S ⊗[R] CartierDual R A) :
    Coalgebra.counit (R := S) (baseChangeAlgEquiv S x) = Coalgebra.counit (R := S) x := by
  induction x using TensorProduct.inductionOn with
  | tmul s φ =>
    change baseChangeAlgEquiv S (s ⊗ₜ φ) ((1 : S) ⊗ₜ[R] (1 : A)) = (φ 1) • s
    simp [Algebra.smul_def, mul_comm]
  | add x y hx hy => simp [hx, hy]

private theorem baseChange_dual_tensor_ext
    {x y : CartierDual S (S ⊗[R] A) ⊗[S] CartierDual S (S ⊗[R] A)}
    (h : ∀ a b, tensorEquiv S (S ⊗[R] A) (S ⊗[R] A) x
        ((1 ⊗ₜ a) ⊗ₜ[S] (1 ⊗ₜ b)) =
      tensorEquiv S (S ⊗[R] A) (S ⊗[R] A) y ((1 ⊗ₜ a) ⊗ₜ[S] (1 ⊗ₜ b))) : x = y := by
  let e := TensorProduct.congr (baseChangeAlgEquiv (R := R) (A := A) S).toLinearEquiv
    (baseChangeAlgEquiv (R := R) (A := A) S).toLinearEquiv
  apply e.symm.injective
  apply baseChange_tensor_ext S
  intro a b
  change tensorEquiv S (S ⊗[R] A) (S ⊗[R] A) (e (e.symm x))
      ((1 ⊗ₜ a) ⊗ₜ[S] (1 ⊗ₜ b)) =
    tensorEquiv S (S ⊗[R] A) (S ⊗[R] A) (e (e.symm y))
      ((1 ⊗ₜ a) ⊗ₜ[S] (1 ⊗ₜ b))
  rw [e.apply_symm_apply, e.apply_symm_apply]
  exact h a b

variable [Coalgebra.IsCocomm R A]

/-- Scalar extension commutes with integral Cartier duality as a Hopf
algebra construction, including its coalgebra structure. -/
def baseChangeBialgEquiv :
    S ⊗[R] CartierDual R A ≃ₐc[S] CartierDual S (S ⊗[R] A) :=
  BialgEquiv.ofAlgEquiv (baseChangeAlgEquiv S)
    (by apply AlgHom.ext; intro x; exact baseChange_counit S x)
    (by
      apply AlgHom.ext
      intro x
      apply baseChange_dual_tensor_ext S
      intro a b
      change baseChangeTensorEquiv S (Coalgebra.comul x) ((1 ⊗ₜ a) ⊗ₜ[S] (1 ⊗ₜ b)) =
        tensorEquiv S (S ⊗[R] A) (S ⊗[R] A) (comul (baseChangeAlgEquiv S x))
          ((1 ⊗ₜ a) ⊗ₜ[S] (1 ⊗ₜ b))
      rw [baseChange_comul_eval, comul_eval, Algebra.TensorProduct.tmul_mul_tmul, one_mul])

end HopfAlgebra.CartierDual
