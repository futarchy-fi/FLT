/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierLinearEvaluation
public import FLT.GroupScheme.CartierDualElementNaturality
public import FLT.GroupScheme.CartierSquareZeroDifferential

/-! # Cotangent contraction for linearly lifted Cartier coefficients -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace HopfAlgebra.CartierDual
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R B] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

/-- Biduality represents arbitrary linear dual coefficients in the original coordinate tensor. -/
def linearTestDualElement (ψ : CartierDual R A →ₗ[R] B) : A ⊗[R] B :=
  coordinateTensorEquiv.symm (ψ.comp linearEquiv.symm.toLinearMap)

/-- The representing tensor has the original coordinate expansion in any basis. -/
theorem linearTestDualElement_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι R A)
    (ψ : CartierDual R A →ₗ[R] B) :
    linearTestDualElement ψ = ∑ i, b i ⊗ₜ[R] ψ (WithConv.toConv (b.coord i)) := by
  classical
  apply (coordinateTensorEquiv (R := R) (A := A) (S := B)).injective
  ext φ
  simp only [linearTestDualElement, LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, map_sum, LinearMap.sum_apply, coordinateTensorEquiv_tmul]
  have h := congrArg (fun f : Module.Dual R A ↦ ψ (linearEquiv.symm f))
    (b.dualBasis.sum_repr φ)
  have hb (i : ι) : linearEquiv.symm (b.dualBasis i) = WithConv.toConv (b.coord i) := by
    apply WithConv.ext
    ext a
    exact b.dualBasis_apply i a
  simpa only [map_sum, map_smul, Module.Basis.dualBasis_repr, hb] using h.symm

/-- Project the lifted coefficients through the actual augmentation quotient. -/
def linearTestDlog (ψ : CartierDual R A →ₗ[R] B) :
    (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent ⊗[R] B :=
  (Bialgebra.counitAlgHom R A).augmentationCotangent.rTensor B (linearTestDualElement ψ)

/-- The lifted cotangent tensor is given by the original augmented coordinates. -/
theorem linearTestDlog_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι R A)
    (ψ : CartierDual R A →ₗ[R] B) :
    linearTestDlog ψ = ∑ i, (Bialgebra.counitAlgHom R A).augmentationCotangent (b i) ⊗ₜ[R]
      ψ (WithConv.toConv (b.coord i)) := by
  rw [linearTestDlog, linearTestDualElement_eq_sum b]
  simp

/-- On algebra characters the lifted tensor is the original dlog tensor. -/
theorem linearTestDlog_algHom (ψ : CartierDual R A →ₐ[R] B) :
    linearTestDlog ψ.toLinearMap = testDlog ψ := by
  rw [linearTestDlog_eq_sum (Module.Free.chooseBasis R A),
    testDlog_eq_sum (Module.Free.chooseBasis R A)]
  rfl

/-- Linear evaluation on an augmented derivative is exactly cotangent contraction. -/
theorem linearTestDlog_pairing (ψ : CartierDual R A →ₗ[R] B)
    (d : (RingHom.ker (Bialgebra.counitAlgHom R A)).Cotangent →ₗ[R] B) :
    LinearMap.mul' R B (d.rTensor B (linearTestDlog ψ)) =
      linearTestEvaluation ψ ((Bialgebra.counitAlgHom R A).augmentationTangentEquiv d).val := by
  rw [linearTestDlog_eq_sum (Module.Free.chooseBasis R A),
    linearTestEvaluation_eq_sum (Module.Free.chooseBasis R A)]
  simp [AlgHom.augmentationTangentEquiv_apply]

/-- Reduction of a linear character lift gives precisely the original reduced dlog tensor. -/
theorem linearTestDlog_reduction {C : Type} [CommRing C] [Algebra R C]
    (q : B →ₐ[R] C) (ψ : CartierDual R A →ₗ[R] B) (χ : CartierDual R A →ₐ[R] C)
    (hψ : q.toLinearMap.comp ψ = χ.toLinearMap) :
    q.toLinearMap.lTensor _ (linearTestDlog ψ) = testDlog χ := by
  rw [linearTestDlog_eq_sum (Module.Free.chooseBasis R A),
    testDlog_eq_sum (Module.Free.chooseBasis R A)]
  simp only [map_sum, LinearMap.lTensor_tmul]
  congr 1
  ext i
  exact congrArg (fun c ↦ _ ⊗ₜ[R] c) (LinearMap.congr_fun hψ _)

end HopfAlgebra.CartierDual
