/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualBaseChange
public import FLT.GroupScheme.HopfTorsor

/-! # Cartier characters on arbitrary integral test algebras -/

@[expose] public noncomputable section
open scoped TensorProduct
open Coalgebra
namespace HopfAlgebra.CartierDual
variable {R A S : Type} [CommRing R] [CommRing A] [CommRing S]
  [Algebra R S] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

/-- Represent any test-algebra-valued linear functional by its integral dual tensor. -/
def testLinearTensor : (A →ₗ[R] S) ≃ₗ[R] S ⊗[R] CartierDual R A :=
  (dualTensorHomEquiv R A S).symm ≪≫ₗ TensorProduct.comm R _ _ ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl R S) linearEquiv.symm

/-- Tensor representation retains the original coordinate evaluation. -/
theorem testLinearTensor_eval (d : A →ₗ[R] S) (a : A) :
    baseChangeAlgEquiv S (testLinearTensor d) (1 ⊗ₜ a) = d a := by
  obtain ⟨t, rfl⟩ := (dualTensorHomEquiv R A S).surjective d
  induction t using TensorProduct.inductionOn with
  | tmul φ s =>
    simp only [testLinearTensor, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      TensorProduct.comm_tmul, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      baseChangeAlgEquiv_tmul, dualTensorHomEquiv_tmul]
    change s * algebraMap R S (φ a) = φ a • s
    rw [Algebra.smul_def, mul_comm]
  | add t u ht hu => simp_all only [map_add, WithConv.ofConv_add, LinearMap.add_apply]

/-- The representing tensor of a point is multiplicative for the original convolution. -/
def testPointTensor : WithConv (A →ₐ[R] S) →* S ⊗[R] CartierDual R A where
  toFun f := testLinearTensor f.ofConv.toLinearMap
  map_one' := by
    apply (baseChangeAlgEquiv (R := R) (A := A) S).injective
    apply WithConv.ext
    apply (TensorProduct.isBaseChange R A S).algHom_ext
    intro a
    change baseChangeAlgEquiv S (testLinearTensor _) (1 ⊗ₜ a) = _
    simp [testLinearTensor_eval, Algebra.smul_def]
  map_mul' f g := by
    apply (baseChangeAlgEquiv (R := R) (A := A) S).injective
    apply WithConv.ext
    apply (TensorProduct.isBaseChange R A S).algHom_ext
    intro a
    rw [map_mul]
    change baseChangeAlgEquiv S (testLinearTensor _) (1 ⊗ₜ a) = _
    rw [testLinearTensor_eval, LinearMap.convMul_apply]
    erw [
      TensorProduct.comul_tmul (R := R) (S := S) (1 : S) a,
      ← (ℛ R a).eq]
    simp [TensorProduct.tmul_sum, testLinearTensor_eval,
      AlgHom.convMul_apply, ← (ℛ R a).eq]

/-- Evaluate an integral dual point on arbitrary linear test coordinates. -/
def testEvaluation (ψ : CartierDual R A →ₐ[R] S) : (A →ₗ[R] S) →ₗ[R] S :=
  ((AlgHom.liftEquiv R S (CartierDual R A) S ψ).toLinearMap.restrictScalars R).comp
    testLinearTensor.toLinearMap

/-- Evaluation of test points is multiplicative. -/
def testCharacterValue (ψ : CartierDual R A →ₐ[R] S) : WithConv (A →ₐ[R] S) →* S :=
  (AlgHom.liftEquiv R S (CartierDual R A) S ψ).toMonoidHom.comp testPointTensor

/-- The character value uses exactly the canonical linear evaluation. -/
theorem testCharacterValue_apply (ψ : CartierDual R A →ₐ[R] S) (f : A →ₐ[R] S) :
    testCharacterValue ψ (WithConv.toConv f) = testEvaluation ψ f.toLinearMap := rfl

/-- The original antipode supplies the inverse of every character value. -/
theorem testCharacterValue_inv (ψ : CartierDual R A →ₐ[R] S) (f : A →ₐ[R] S) :
    testCharacterValue ψ (WithConv.toConv f) *
      testCharacterValue ψ (WithConv.toConv (f.comp (antipodeAlgHom R A))) = 1 := by
  rw [mul_comm, ← map_mul]
  have h := conv_antipode_mul f
  rw [h, map_one]

/-- The finite Cartier character on integral test points takes values in actual units. -/
def testCharacter (ψ : CartierDual R A →ₐ[R] S) : WithConv (A →ₐ[R] S) →* Sˣ where
  toFun f := Units.mkOfMulEqOne _ _ (testCharacterValue_inv ψ f.ofConv)
  map_one' := by apply Units.ext; exact map_one (testCharacterValue ψ)
  map_mul' f g := by apply Units.ext; exact map_mul (testCharacterValue ψ) f g

/-- Forgetting units recovers the original coordinate evaluation. -/
@[simp] theorem testCharacter_coe (ψ : CartierDual R A →ₐ[R] S) (f : A →ₐ[R] S) :
    (testCharacter ψ (WithConv.toConv f) : S) = testEvaluation ψ f.toLinearMap := rfl

end HopfAlgebra.CartierDual
