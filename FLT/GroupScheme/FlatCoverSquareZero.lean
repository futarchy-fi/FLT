/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FlatCoverReductionKernel
public import FLT.GroupScheme.SquareZeroReductionBaseChange
public import FLT.GroupScheme.SquareZeroAugmentationPoints

/-! # Square-zero kernels and their annihilators on actual flat covers -/

@[expose] public noncomputable section
open TensorProduct
namespace Algebra
variable (B C D : Type*) [CommRing B] [CommRing C] [CommRing D]
  [Algebra B C] [Algebra B D]

/-- The actual cover reduction retains the square-zero kernel. -/
theorem squareZero_coverReduction (hq : Function.Surjective (algebraMap B C))
    (hJ : RingHom.ker (algebraMap B C) ^ 2 = ⊥) :
    RingHom.ker (TensorProduct.includeLeft : D →ₐ[B] D ⊗[B] C) ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro d hd e he
  change d * e = 0
  apply (TensorProduct.rid B D D).symm.injective
  rw [map_mul, map_zero]
  exact AlgHom.squareZeroKernel_mul _
    (AlgHom.squareZero_tensor_reduction D (Algebra.ofId B C) hq hJ)
    ((coverReductionKernelRidEquiv B C D).symm ⟨d, hd⟩)
    ((coverReductionKernelRidEquiv B C D).symm ⟨e, he⟩)

/-- A flat cover preserves the specified annihilator of the actual reduction kernel. -/
theorem nsmul_coverReduction_kernel [Module.Flat B D] (N : ℕ)
    (hN : ∀ b : RingHom.ker (algebraMap B C), N • b = 0)
    (z : RingHom.ker (TensorProduct.includeLeft : D →ₐ[B] D ⊗[B] C)) : N • z = 0 := by
  obtain ⟨w, rfl⟩ := (flatCoverReductionKernelEquiv B C D).surjective z
  rw [← map_nsmul]
  have hw : N • w = 0 := by
    induction w using TensorProduct.inductionOn with
    | tmul d b => rw [← TensorProduct.tmul_smul, hN, TensorProduct.tmul_zero]
    | add x y hx hy => rw [nsmul_add, hx, hy, add_zero]
  rw [hw, map_zero]

end Algebra
