/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualElementNaturality

/-! # Original integral dual points multiply their representing tensors -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace HopfAlgebra.CartierDual
variable {R A S : Type} [CommRing R] [CommRing A] [CommRing S]
  [Algebra R S] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Free R A]

local instance dualCoordinateFree : Module.Free R (CartierDual R A) :=
  Module.Free.of_equiv (linearEquiv (R := R) (A := A)).symm

/-- Integral biduality on the coefficient tensor, retaining the original tensor order. -/
def testBidualTensorEquiv :
    A ⊗[R] S ≃ₐ[R] S ⊗[R] CartierDual R (CartierDual R A) :=
  (Algebra.TensorProduct.comm R A S).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[R] S) bidualAlgEquiv)

/-- Bidual tensor evaluation is exactly the original coordinate-functional evaluation. -/
theorem testBidualTensorEquiv_eval (t : A ⊗[R] S) (φ : CartierDual R A) :
    baseChangeAlgEquiv S (testBidualTensorEquiv t) (1 ⊗ₜ φ) =
      coordinateTensorEquiv t φ.ofConv := by
  induction t using TensorProduct.inductionOn with
  | tmul a s =>
    simp [testBidualTensorEquiv, Algebra.smul_def, mul_comm]
  | add t u ht hu => simp only [map_add, WithConv.ofConv_add, LinearMap.add_apply, ht, hu]

/-- The canonical tensor is also the actual convolution point tensor under integral biduality. -/
theorem testBidualTensorEquiv_dualElement (ψ : CartierDual R A →ₐ[R] S) :
    testBidualTensorEquiv (testDualElement ψ) = testPointTensor (WithConv.toConv ψ) := by
  apply (baseChangeAlgEquiv (R := R) (A := CartierDual R A) S).injective
  apply WithConv.ext
  apply (TensorProduct.isBaseChange R (CartierDual R A) S).algHom_ext
  intro φ
  erw [testBidualTensorEquiv_eval, coordinateTensorEquiv_dualElement]
  exact (testLinearTensor_eval ψ.toLinearMap φ).symm

/-- The original convolution law gives multiplication of the actual representing elements. -/
theorem testDualElement_mul (ψ χ : WithConv (CartierDual R A →ₐ[R] S)) :
    testDualElement (ψ * χ).ofConv = testDualElement ψ.ofConv * testDualElement χ.ofConv := by
  apply (testBidualTensorEquiv (R := R) (A := A) (S := S)).injective
  rw [map_mul, testBidualTensorEquiv_dualElement, testBidualTensorEquiv_dualElement,
    testBidualTensorEquiv_dualElement]
  exact map_mul testPointTensor ψ χ

/-- The trivial original dual point has representing element one. -/
@[simp] theorem testDualElement_one :
    testDualElement (1 : WithConv (CartierDual R A →ₐ[R] S)).ofConv = 1 := by
  apply (testBidualTensorEquiv (R := R) (A := A) (S := S)).injective
  rw [testBidualTensorEquiv_dualElement, map_one, map_one]

omit [Coalgebra.IsCocomm R A] in
/-- Every original character's representing element has augmentation one. -/
theorem testDualElement_counit (ψ : CartierDual R A →ₐ[R] S) :
    TensorProduct.lid R S
      ((Bialgebra.counitAlgHom R A).toLinearMap.rTensor S (testDualElement ψ)) = 1 := by
  have h (t : A ⊗[R] S) :
      TensorProduct.lid R S ((Bialgebra.counitAlgHom R A).toLinearMap.rTensor S t) =
        coordinateTensorEquiv t (Coalgebra.counit (R := R)) := by
    induction t using TensorProduct.inductionOn with
    | tmul a s => rfl
    | add t u ht hu => simp only [map_add, LinearMap.add_apply, ht, hu]
  rw [h, coordinateTensorEquiv_dualElement]
  exact map_one ψ

end HopfAlgebra.CartierDual
