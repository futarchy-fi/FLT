/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FlatCoverReductionKernel
public import FLT.GroupScheme.AmitsurDegreeOneMaps

/-! # The original reduction kernel inside overlap tensor rings -/

@[expose] public noncomputable section
open TensorProduct
namespace Algebra
variable (B C D : Type*) [CommRing B] [CommRing C] [CommRing D]
  [Algebra B C] [Algebra B D] [Module.Flat B D]

/-- Inclusion of the tensor kernel into the actual cover ring. -/
def coverKernelInclusion : D ⊗[B] RingHom.ker (algebraMap B C) →ₗ[B] D :=
  ((RingHom.ker (TensorProduct.includeLeft : D →ₐ[B] D ⊗[B] C)).restrictScalars B).subtype.comp
    ((flatCoverReductionKernelEquiv B C D).toLinearMap.restrictScalars B)

/-- The kernel inclusion is injective because the cover is flat. -/
theorem coverKernelInclusion_injective : Function.Injective (coverKernelInclusion B C D) :=
  Subtype.val_injective.comp (flatCoverReductionKernelEquiv B C D).injective

/-- Pure tensors map by scalar multiplication in the original cover. -/
@[simp] theorem coverKernelInclusion_tmul (d : D) (b : RingHom.ker (algebraMap B C)) :
    coverKernelInclusion B C D (d ⊗ₜ[B] b) = (b : B) • d := rfl

/-- The double tensor kernel is the actual kernel on the double overlap. -/
def doubleCoverKernelEquiv :
    D ⊗[B] (D ⊗[B] RingHom.ker (algebraMap B C)) ≃ₗ[B]
      RingHom.ker (TensorProduct.includeLeft : (D ⊗[B] D) →ₐ[B] (D ⊗[B] D) ⊗[B] C) :=
  (_root_.TensorProduct.assoc B D D _).symm.trans
    ((flatCoverReductionKernelEquiv B C (D ⊗[B] D)).restrictScalars B)

/-- The double comparison is the tensor of the original kernel inclusion. -/
theorem doubleCoverKernelEquiv_coe (z : D ⊗[B] (D ⊗[B] RingHom.ker (algebraMap B C))) :
    (doubleCoverKernelEquiv B C D z : D ⊗[B] D) =
      (coverKernelInclusion B C D).lTensor D z := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul d z =>
    induction z using _root_.TensorProduct.inductionOn with
    | tmul e b =>
      change (b : B) • (d ⊗ₜ[B] e) = d ⊗ₜ[B] ((b : B) • e)
      exact (_root_.TensorProduct.tmul_smul _ _ _).symm
    | add x y hx hy => simp only [tmul_add, map_add, Submodule.coe_add, hx, hy]
  | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]

/-- Inclusion on triple kernel tensors is injective as well. -/
theorem tripleCoverKernelInclusion_injective :
    Function.Injective (((coverKernelInclusion B C D).lTensor D).lTensor D) :=
  Module.Flat.lTensor_preserves_injective_linearMap _
    (Module.Flat.lTensor_preserves_injective_linearMap _
      (coverKernelInclusion_injective B C D))

end Algebra
