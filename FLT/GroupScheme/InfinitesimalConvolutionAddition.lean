/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SquareZeroAugmentationPoints
public import FLT.GroupScheme.SquareZeroConvolution
public import Mathlib.RingTheory.Bialgebra.Convolution

/-! # Convolution is addition on the actual square-zero augmentation kernel -/

@[expose] public noncomputable section
open WithConv
namespace HopfAlgebra
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Bialgebra R A] [Algebra R B] [Algebra R C]
  (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥)

include hJ in
/-- The product of any two kernel-valued linear functionals is zero under convolution. -/
theorem convMul_eq_zero_of_kernel (d e : A →ₗ[R] B)
    (hd : ∀ a, d a ∈ RingHom.ker q) (he : ∀ a, e a ∈ RingHom.ker q) :
    toConv d * toConv e = 0 := by
  apply WithConv.ext
  ext a
  rw [(Coalgebra.Repr.arbitrary R a).convMul_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact AlgHom.squareZeroKernel_mul q hJ
    ⟨_, hd ((Coalgebra.Repr.arbitrary R a).left i)⟩
    ⟨_, he ((Coalgebra.Repr.arbitrary R a).right i)⟩

/-- Convolution preserves the actual augmentation kernel. -/
def augmentationKernelConv
    (f g : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) :
    (Bialgebra.counitAlgHom R A).AugmentationPointKernel q :=
  ⟨(toConv f.val * toConv g.val).ofConv, by
    rw [AlgHom.comp_convMul_distrib, f.property, g.property]
    exact congrArg ofConv (one_mul (1 : WithConv (A →ₐ[R] C)))⟩

/-- The tangent of the group product is the sum of the original tangent functionals. -/
theorem augmentationPointToTangent_conv
    (f g : (Bialgebra.counitAlgHom R A).AugmentationPointKernel q) :
    AlgHom.augmentationPointToTangent _ q hJ (augmentationKernelConv q f g) =
      AlgHom.augmentationPointToTangent _ q hJ f +
        AlgHom.augmentationPointToTangent _ q hJ g := by
  let d := AlgHom.augmentationPointToTangent _ q hJ f
  let e := AlgHom.augmentationPointToTangent _ q hJ g
  have hz := convMul_eq_zero_of_kernel q hJ
    (f.val.toLinearMap - (1 : WithConv (A →ₗ[R] B)).ofConv)
    (g.val.toLinearMap - (1 : WithConv (A →ₗ[R] B)).ofConv)
    (fun a ↦ (d.val a).property) (fun a ↦ (e.val a).property)
  change (toConv f.val.toLinearMap - 1) * (toConv g.val.toLinearMap - 1) = 0 at hz
  rw [sub_mul, mul_sub, mul_sub, mul_one, one_mul, one_mul] at hz
  have heq : toConv f.val.toLinearMap * toConv g.val.toLinearMap - 1 =
      (toConv f.val.toLinearMap - 1) + (toConv g.val.toLinearMap - 1) := by
    calc
      _ = ((toConv f.val.toLinearMap * toConv g.val.toLinearMap -
          toConv f.val.toLinearMap) - (toConv g.val.toLinearMap - 1)) +
          ((toConv f.val.toLinearMap - 1) + (toConv g.val.toLinearMap - 1)) := by abel
      _ = _ := by rw [hz, zero_add]
  apply Subtype.ext
  ext a
  exact congrArg (fun t : WithConv (A →ₗ[R] B) ↦ t.ofConv a) heq

end HopfAlgebra
