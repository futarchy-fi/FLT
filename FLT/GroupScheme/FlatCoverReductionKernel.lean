/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FlatReductionKernel

/-! # The actual reduction kernel on a flat cover of the test algebra -/

@[expose] public noncomputable section
open TensorProduct
namespace Algebra
variable (B C D : Type*) [CommRing B] [CommRing C] [CommRing D]
  [Algebra B C] [Algebra B D]

/-- Removing tensor-with-B commutes with the actual cover reduction. -/
theorem coverReduction_rid (z : D ⊗[B] B) :
    (TensorProduct.includeLeft : D →ₐ[B] D ⊗[B] C)
      (TensorProduct.rid B D D z) =
    TensorProduct.map (AlgHom.id B D) (Algebra.ofId B C) z := by
  induction z using TensorProduct.inductionOn with
  | tmul d b =>
    simp only [TensorProduct.rid_tmul, map_smul, TensorProduct.includeLeft_apply,
      TensorProduct.map_tmul, AlgHom.id_apply]
    rw [← TensorProduct.tmul_smul]
    simp [Algebra.smul_def]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The tensor reduction kernel identifies with the kernel on the cover itself. -/
def coverReductionKernelRidEquiv :
    RingHom.ker (TensorProduct.map (AlgHom.id B D) (Algebra.ofId B C)) ≃ₗ[D]
      RingHom.ker (TensorProduct.includeLeft : D →ₐ[B] D ⊗[B] C) where
  toFun z := ⟨TensorProduct.rid B D D z.val, by
    change (TensorProduct.includeLeft : D →ₐ[B] D ⊗[B] C) _ = 0
    rw [coverReduction_rid]
    exact z.property⟩
  invFun z := ⟨(TensorProduct.rid B D D).symm z.val, by
    change TensorProduct.map (AlgHom.id B D) (Algebra.ofId B C) _ = 0
    rw [← coverReduction_rid, AlgEquiv.apply_symm_apply]
    exact z.property⟩
  left_inv z := by apply Subtype.ext; exact AlgEquiv.symm_apply_apply _ _
  right_inv z := by apply Subtype.ext; exact AlgEquiv.apply_symm_apply _ _
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' d x := by apply Subtype.ext; exact map_smul _ _ _

/-- Tensoring the original kernel gives the actual reduction kernel on a flat cover. -/
def flatCoverReductionKernelEquiv [Module.Flat B D] :
    D ⊗[B] RingHom.ker (algebraMap B C) ≃ₗ[D]
      RingHom.ker (TensorProduct.includeLeft : D →ₐ[B] D ⊗[B] C) :=
  (AlgHom.flatReductionKernelEquiv D (Algebra.ofId B C)).trans
    (coverReductionKernelRidEquiv B C D)

/-- The comparison is multiplication by the original kernel element. -/
theorem flatCoverReductionKernelEquiv_tmul [Module.Flat B D]
    (d : D) (b : RingHom.ker (algebraMap B C)) :
    (flatCoverReductionKernelEquiv B C D (d ⊗ₜ[B] b) : D) = (b : B) • d := rfl

end Algebra
