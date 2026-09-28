/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualAlgebra

/-!
# The coalgebra underlying integral Cartier duality

Multiplication and the unit of a finite projective algebra transpose to
comultiplication and the counit on its integral linear dual.
-/

@[expose] public noncomputable section

open scoped TensorProduct


namespace HopfAlgebra.CartierDual

section Tensor

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N]
  [Module.Projective R M] [Module.Projective R N]

/-- The canonical tensor comparison for finite projective convolution duals. -/
def tensorEquiv : CartierDual R M ⊗[R] CartierDual R N ≃ₗ[R]
    Module.Dual R (M ⊗[R] N) :=
  (TensorProduct.congr (WithConv.linearEquiv R _) (WithConv.linearEquiv R _)).trans
    (TensorProduct.dualDistribEquiv R M N)

/-- Evaluation of the tensor comparison on pure tensors. -/
@[simp] theorem tensorEquiv_tmul (φ : CartierDual R M) (ψ : CartierDual R N)
    (m : M) (n : N) : tensorEquiv R M N (φ ⊗ₜ ψ) (m ⊗ₜ n) = φ m * ψ n := by
  simp [tensorEquiv, mul_comm]

/-- Evaluations on pure tensors separate tensors of integral duals. -/
theorem tensor_ext {x y : CartierDual R M ⊗[R] CartierDual R N}
    (h : ∀ m n, tensorEquiv R M N x (m ⊗ₜ n) = tensorEquiv R M N y (m ⊗ₜ n)) : x = y :=
  (tensorEquiv R M N).injective (TensorProduct.ext' h)

end Tensor

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [Module.Finite R A] [Module.Projective R A]

/-- Transpose multiplication to obtain integral dual comultiplication. -/
def comul : CartierDual R A →ₗ[R] CartierDual R A ⊗[R] CartierDual R A :=
  (tensorEquiv R A A).symm.toLinearMap ∘ₗ (LinearMap.mul' R A).dualMap ∘ₗ
    linearEquiv.toLinearMap

/-- The dual counit evaluates a functional at the unit. -/
def counit : CartierDual R A →ₗ[R] R :=
  (Module.Dual.eval R A 1).comp linearEquiv.toLinearMap

/-- The transpose comultiplication evaluates by multiplication in the source. -/
@[simp] theorem comul_eval (φ : CartierDual R A) (a b : A) :
    tensorEquiv R A A (comul φ) (a ⊗ₜ b) = φ (a * b) := by
  simp [comul]

omit [Module.Finite R A] [Module.Projective R A] in
/-- The transpose counit is evaluation at one. -/
@[simp] theorem counit_apply (φ : CartierDual R A) : counit φ = φ 1 := rfl

/-- Evaluate three dual tensor factors against three source factors. -/
def tripleEquiv : CartierDual R A ⊗[R] (CartierDual R A ⊗[R] CartierDual R A) ≃ₗ[R]
    Module.Dual R (A ⊗[R] (A ⊗[R] A)) :=
  (TensorProduct.congr linearEquiv (tensorEquiv R A A)).trans
    (TensorProduct.dualDistribEquiv R A (A ⊗[R] A))

/-- The threefold comparison evaluates a pure tensor by three evaluations. -/
@[simp] theorem tripleEquiv_tmul (φ ψ χ : CartierDual R A) (a b c : A) :
    tripleEquiv (φ ⊗ₜ (ψ ⊗ₜ χ)) (a ⊗ₜ (b ⊗ₜ c)) = φ a * (ψ b * χ c) := by
  simp [tripleEquiv, mul_comm]

private theorem tripleEquiv_left (φ : CartierDual R A)
    (t : CartierDual R A ⊗[R] CartierDual R A) (a b c : A) :
    tripleEquiv (φ ⊗ₜ t) (a ⊗ₜ (b ⊗ₜ c)) =
      φ a * tensorEquiv R A A t (b ⊗ₜ c) := by
  induction t using TensorProduct.inductionOn with
  | tmul ψ χ => simp
  | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy, mul_add]

private theorem tripleEquiv_right (t : CartierDual R A ⊗[R] CartierDual R A)
    (χ : CartierDual R A) (a b c : A) :
    tripleEquiv (TensorProduct.assoc R _ _ _ (t ⊗ₜ χ)) (a ⊗ₜ (b ⊗ₜ c)) =
      tensorEquiv R A A t (a ⊗ₜ b) * χ c := by
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ => simp [mul_assoc]
  | add x y hx hy => simp [TensorProduct.add_tmul, hx, hy, add_mul]

private theorem coassoc_left_eval (t : CartierDual R A ⊗[R] CartierDual R A)
    (a b c : A) :
    tripleEquiv (TensorProduct.assoc R _ _ _ (comul.rTensor _ t)) (a ⊗ₜ (b ⊗ₜ c)) =
      tensorEquiv R A A t ((a * b) ⊗ₜ c) := by
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ => simp [tripleEquiv_right]
  | add x y hx hy => simp [hx, hy]

private theorem coassoc_right_eval (t : CartierDual R A ⊗[R] CartierDual R A)
    (a b c : A) :
    tripleEquiv (comul.lTensor _ t) (a ⊗ₜ (b ⊗ₜ c)) =
      tensorEquiv R A A t (a ⊗ₜ (b * c)) := by
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ => simp [tripleEquiv_left]
  | add x y hx hy => simp [hx, hy]

/-- The transposed multiplication is coassociative. -/
theorem coassoc : (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ comul.rTensor _ ∘ₗ comul =
    comul.lTensor _ ∘ₗ (comul (R := R) (A := A)) := by
  ext φ : 1
  apply tripleEquiv.injective
  apply TensorProduct.ext_threefold'
  intro a b c
  simp [coassoc_left_eval, coassoc_right_eval, mul_assoc]

private theorem counit_left_eval (t : CartierDual R A ⊗[R] CartierDual R A) (a : A) :
    (TensorProduct.lid R (CartierDual R A) (counit.rTensor _ t)) a =
      tensorEquiv R A A t (1 ⊗ₜ a) := by
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ => simp
  | add x y hx hy => simp [hx, hy]

private theorem counit_right_eval (t : CartierDual R A ⊗[R] CartierDual R A) (a : A) :
    (TensorProduct.rid R (CartierDual R A) (counit.lTensor _ t)) a =
      tensorEquiv R A A t (a ⊗ₜ 1) := by
  induction t using TensorProduct.inductionOn with
  | tmul φ ψ => simp [mul_comm]
  | add x y hx hy => simp [hx, hy]

/-- Transposed multiplication and the unit define a coalgebra on the dual. -/
instance instCoalgebra : Coalgebra R (CartierDual R A) where
  comul := comul
  counit := counit
  coassoc := coassoc
  rTensor_counit_comp_comul := by
    ext φ : 1
    apply (TensorProduct.lid R (CartierDual R A)).injective
    apply WithConv.ext
    ext a
    simpa using counit_left_eval (comul φ) a
  lTensor_counit_comp_comul := by
    ext φ : 1
    apply (TensorProduct.rid R (CartierDual R A)).injective
    apply WithConv.ext
    ext a
    simpa using counit_right_eval (comul φ) a

/-- Commutativity of the original coordinate algebra gives cocommutativity
of the dual coalgebra. -/
instance instIsCocomm : Coalgebra.IsCocomm R (CartierDual R A) where
  comm_comp_comul := by
    ext φ : 1
    apply tensor_ext R A A
    intro a b
    have h (t : CartierDual R A ⊗[R] CartierDual R A) :
        tensorEquiv R A A (TensorProduct.comm R _ _ t) (a ⊗ₜ b) =
          tensorEquiv R A A t (b ⊗ₜ a) := by
      induction t using TensorProduct.inductionOn with
      | tmul ψ χ => simp [mul_comm]
      | add x y hx hy => simp [hx, hy]
    change tensorEquiv R A A (TensorProduct.comm R _ _ (comul φ)) (a ⊗ₜ b) =
      tensorEquiv R A A (comul φ) (a ⊗ₜ b)
    exact (h (comul φ)).trans (by simp [mul_comm])

end HopfAlgebra.CartierDual
