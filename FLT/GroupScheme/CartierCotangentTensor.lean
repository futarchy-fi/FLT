/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierTestNaturality
public import FLT.Mathlib.RingTheory.AugmentationTangentEquiv

/-! # The canonical cotangent tensor of an integral Cartier character -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace HopfAlgebra.CartierDual
variable {R A S : Type} [CommRing R] [CommRing A] [CommRing S]
  [Algebra R S] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

/-- Integral biduality represents a dual point by an element of the original coordinates. -/
def testDualElement (ψ : CartierDual R A →ₐ[R] S) : A ⊗[R] S :=
  (TensorProduct.congr (Module.evalEquiv R A) (LinearEquiv.refl R S)).symm
    ((dualTensorHomEquiv R (Module.Dual R A) S).symm
      (ψ.toLinearMap.comp linearEquiv.symm.toLinearMap))

/-- The representing element is the same finite sum in every basis. -/
theorem testDualElement_eq_sum {ι : Type} [Fintype ι]
    (b : Module.Basis ι R A) (ψ : CartierDual R A →ₐ[R] S) :
    testDualElement ψ = ∑ i, b i ⊗ₜ[R] ψ (WithConv.toConv (b.coord i)) := by
  classical
  apply (TensorProduct.congr (Module.evalEquiv R A) (LinearEquiv.refl R S)).injective
  apply (dualTensorHomEquiv R (Module.Dual R A) S).injective
  ext φ
  simp only [testDualElement, LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe,
    map_sum, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    LinearMap.sum_apply, dualTensorHomEquiv_tmul, Module.evalEquiv_apply, Module.Dual.eval_apply]
  have h := congrArg (fun f : Module.Dual R A ↦ ψ (linearEquiv.symm f)) (b.dualBasis.sum_repr φ)
  have hb (i : ι) : linearEquiv.symm (b.dualBasis i) = WithConv.toConv (b.coord i) := by
    apply WithConv.ext
    ext a
    exact b.dualBasis_apply i a
  simpa only [map_sum, map_smul, Module.Basis.dualBasis_repr, hb,
    AlgHom.toLinearMap_apply] using h.symm

/-- Projecting the actual representing element to the augmentation quotient gives dlog at one. -/
def testDlog (ψ : CartierDual R A →ₐ[R] S) :
    (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent ⊗[R] S :=
  (Bialgebra.counitAlgHom R A).augmentationCotangent.rTensor S (testDualElement ψ)

/-- The dlog tensor uses the original augmentation representatives, in every basis. -/
theorem testDlog_eq_sum {ι : Type} [Fintype ι]
    (b : Module.Basis ι R A) (ψ : CartierDual R A →ₐ[R] S) :
    testDlog ψ = ∑ i, (Bialgebra.counitAlgHom R A).augmentationCotangent (b i) ⊗ₜ[R]
      ψ (WithConv.toConv (b.coord i)) := by
  rw [testDlog, testDualElement_eq_sum b]
  simp

/-- Contraction of the actual dlog tensor with a cotangent functional. -/
def testDlogPairing (ψ : CartierDual R A →ₐ[R] S)
    (d : (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent →ₗ[R] S) : S :=
  LinearMap.mul' R S (d.rTensor S (testDlog ψ))

/-- The cotangent tensor differentiates precisely the original Cartier evaluation. -/
theorem testDlogPairing_eq (ψ : CartierDual R A →ₐ[R] S)
    (d : (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent →ₗ[R] S) :
    testDlogPairing ψ d =
      testEvaluation ψ ((Bialgebra.counitAlgHom R A).augmentationTangentEquiv d).val := by
  let b := Module.Free.chooseBasis R A
  rw [testDlogPairing, testDlog_eq_sum b, testEvaluation_eq_sum b]
  simp [AlgHom.augmentationTangentEquiv_apply]

end HopfAlgebra.CartierDual
