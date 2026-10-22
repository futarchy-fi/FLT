/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatExtensionKernelAnnihilation
public import FLT.Mazur.IdealInclusionFlatExtension
public import FLT.Mazur.IdealTensorKernelFinite

/-!
# Killing the ideal obstruction only after a flat target extension

The target comparison is the actual algebra map tensored with the ideal.
Flat exactness and tensor cancellation prove injectivity in the extension from
vanishing there, without asserting that the original obstruction was zero.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FlatTargetObstructionMap
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (T : Type*) [CommRing T] [Algebra R T] [Algebra A T] [IsScalarTower R A T]

/-- The actual target extension on the ideal tensor module. -/
def comparison (I : Ideal R) : A ⊗[R] I →ₗ[R] T ⊗[R] I :=
  (IsScalarTower.toAlgHom R A T).toLinearMap.rTensor I

/-- On generators this is the target algebra map and the unchanged ideal. -/
theorem comparison_tmul (I : Ideal R) (a : A) (i : I) :
    comparison T I (a ⊗ₜ[R] i) = algebraMap A T a ⊗ₜ[R] i := rfl

/-- Cancelling the extension unit gives exactly the actual comparison. -/
theorem comparison_cancel (I : Ideal R) (z : A ⊗[R] I) :
    AlgebraTensorModule.cancelBaseChange R A T T I (1 ⊗ₜ[A] z) = comparison T I z := by
  induction z with
  | tmul a i =>
    simp only [AlgebraTensorModule.cancelBaseChange_tmul, comparison_tmul,
      Algebra.smul_def, mul_one]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/-- Killing the old kernel in a flat target extension makes its ideal inclusion injective. -/
theorem inclusion_injective [Module.Flat A T] (I : Ideal R)
    (h : ∀ z : IdealTensorKernel.obstruction (S := A) I, comparison T I z.val = 0) :
    Function.Injective (FCurve.idealTensorInclusion (S := T) I) := by
  have hinj := FlatExtensionKernelAnnihilation.lTensor_injective T
    (FCurve.idealTensorInclusion (S := A) I) (fun z ↦ ?_)
  · intro x y hxy
    apply (AlgebraTensorModule.cancelBaseChange R A T T I).symm.injective
    apply hinj
    apply (AlgebraTensorModule.rid A T T).injective
    rw [← IdealInclusionFlatExtension.inclusion_cancel T I,
      ← IdealInclusionFlatExtension.inclusion_cancel T I,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hxy
  apply (AlgebraTensorModule.cancelBaseChange R A T T I).injective
  rw [comparison_cancel, h z, map_zero]

end FLT.Mazur.FlatTargetObstructionMap
