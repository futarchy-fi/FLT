/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierTestCoefficients
public import FLT.GroupScheme.SquareZeroAugmentationPoints

/-! # Cartier evaluation with linearly lifted character coefficients -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace HopfAlgebra.CartierDual
variable {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

/-- The original tensor pairing also accepts a linear lift of the dual coefficients. -/
def linearTestEvaluation (ψ : CartierDual R A →ₗ[R] B) : (A →ₗ[R] B) →ₗ[R] B :=
  (LinearMap.mul' R B).comp ((ψ.lTensor B).comp testLinearTensor.toLinearMap)

/-- A basis computes the pairing but is not part of its definition. -/
theorem linearTestEvaluation_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι R A)
    (ψ : CartierDual R A →ₗ[R] B) (d : A →ₗ[R] B) :
    linearTestEvaluation ψ d = ∑ i, d (b i) * ψ (WithConv.toConv (b.coord i)) := by
  unfold linearTestEvaluation
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    testLinearTensor_eq_sum b]
  simp

/-- On actual characters this is the previously defined Cartier evaluation. -/
theorem linearTestEvaluation_algHom (ψ : CartierDual R A →ₐ[R] B) :
    linearTestEvaluation ψ.toLinearMap = testEvaluation ψ := by
  ext d
  rw [linearTestEvaluation_eq_sum (Module.Free.chooseBasis R A),
    testEvaluation_eq_sum (Module.Free.chooseBasis R A)]
  rfl

/-- Linear coefficient evaluation commutes with the actual reduction. -/
theorem linearTestEvaluation_coefficients (q : B →ₐ[R] C)
    (ψ : CartierDual R A →ₗ[R] B) (d : A →ₗ[R] B) :
    q (linearTestEvaluation ψ d) =
      linearTestEvaluation (q.toLinearMap.comp ψ) (q.toLinearMap.comp d) := by
  rw [linearTestEvaluation_eq_sum (Module.Free.chooseBasis R A),
    linearTestEvaluation_eq_sum (Module.Free.chooseBasis R A)]
  simp

/-- On a kernel-valued tangent, congruent dual coefficient lifts give exactly the same value. -/
theorem linearTestEvaluation_lift_independent (q : B →ₐ[R] C)
    (hJ : RingHom.ker q ^ 2 = ⊥) (ψ χ : CartierDual R A →ₗ[R] B)
    (hψ : q.toLinearMap.comp ψ = q.toLinearMap.comp χ)
    (d : A →ₗ[R] B) (hd : ∀ a, d a ∈ RingHom.ker q) :
    linearTestEvaluation ψ d = linearTestEvaluation χ d := by
  rw [linearTestEvaluation_eq_sum (Module.Free.chooseBasis R A),
    linearTestEvaluation_eq_sum (Module.Free.chooseBasis R A)]
  apply Finset.sum_congr rfl
  intro i _
  apply sub_eq_zero.mp
  rw [← mul_sub]
  exact AlgHom.squareZeroKernel_mul q hJ ⟨_, hd _⟩ ⟨_, by
    change q (ψ _ - χ _) = 0
    rw [map_sub, show q (ψ _) = q (χ _) from LinearMap.congr_fun hψ _, sub_self]⟩

/-- A kernel-valued tangent pairs into the actual reduction kernel. -/
theorem linearTestEvaluation_mem_kernel (q : B →ₐ[R] C)
    (ψ : CartierDual R A →ₗ[R] B) (d : A →ₗ[R] B)
    (hd : ∀ a, d a ∈ RingHom.ker q) :
    linearTestEvaluation ψ d ∈ RingHom.ker q := by
  rw [linearTestEvaluation_eq_sum (Module.Free.chooseBasis R A)]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_right _ _ (hd _)

end HopfAlgebra.CartierDual
