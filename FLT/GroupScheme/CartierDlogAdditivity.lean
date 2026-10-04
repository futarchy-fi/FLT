/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualElementMultiplication

/-! # Additivity of the original integral Cartier differential -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace HopfAlgebra.CartierDual
variable {R A S : Type} [CommRing R] [CommRing A] [CommRing S]
  [Algebra R S] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]
  [Module.Finite R A] [Module.Free R A]

omit [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Free R A] in
/-- The original augmentation differential obeys Leibniz after integral coefficient extension. -/
theorem augmentationTensor_leibniz (t u : A ⊗[R] S) :
    let ε := Bialgebra.counitAlgHom R A
    let D := (TensorProduct.comm R _ S).toLinearMap.comp (ε.augmentationCotangent.rTensor S)
    let E := (TensorProduct.lid R S).toLinearMap.comp (ε.toLinearMap.rTensor S)
    D (t * u) = E t • D u + E u • D t := by
  dsimp only
  induction t using TensorProduct.inductionOn with
  | tmul a s =>
    induction u using TensorProduct.inductionOn with
    | tmul b z =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.comp_apply,
        LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
        TensorProduct.lid_tmul, AlgHom.augmentationCotangent_mul,
        TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply,
        AlgHom.toLinearMap_apply]
      congr 1 <;> congr 1 <;> ring
    | add u v hu hv =>
      simp only [mul_add, map_add, hu, hv, smul_add, add_smul]
      abel
  | add t v ht hv =>
    simp only [add_mul, map_add, ht, hv, smul_add, add_smul]
    abel

/-- Multiplication of actual integral dual points adds their original cotangent tensors. -/
theorem testDlog_mul (ψ χ : WithConv (CartierDual R A →ₐ[R] S)) :
    testDlog (ψ * χ).ofConv = testDlog ψ.ofConv + testDlog χ.ofConv := by
  apply (TensorProduct.comm R _ S).injective
  have h := augmentationTensor_leibniz (testDualElement ψ.ofConv) (testDualElement χ.ofConv)
  dsimp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  rw [testDualElement_counit, testDualElement_counit, one_smul, one_smul] at h
  simpa only [testDlog, testDualElement_mul, map_add, add_comm] using h

/-- The trivial dual point has zero integral differential. -/
@[simp] theorem testDlog_one :
    testDlog (1 : WithConv (CartierDual R A →ₐ[R] S)).ofConv = 0 := by
  rw [testDlog, testDualElement_one, Algebra.TensorProduct.one_def,
    LinearMap.rTensor_tmul, AlgHom.augmentationCotangent_one, TensorProduct.zero_tmul]

/-- The integral dlog is a homomorphism for the original convolution group law. -/
def testDlogHom : WithConv (CartierDual R A →ₐ[R] S) →* Multiplicative
    ((RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent ⊗[R] S) where
  toFun ψ := Multiplicative.ofAdd (testDlog ψ.ofConv)
  map_one' := testDlog_one
  map_mul' := testDlog_mul

end HopfAlgebra.CartierDual
