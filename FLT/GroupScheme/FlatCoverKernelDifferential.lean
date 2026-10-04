/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FlatCoverKernelAmitsur

/-! # Kernel-valued Amitsur differentials are the actual overlap maps -/

@[expose] public noncomputable section
open TensorProduct
namespace Algebra
variable (B D : Type*) [CommRing B] [CommRing D] [Algebra B D]

/-- Pull a double overlap to the last two coordinates of a triple overlap. -/
abbrev overlapCoface₀ : D ⊗[B] D →ₐ[B] D ⊗[B] (D ⊗[B] D) := TensorProduct.includeRight

/-- Pull a double overlap to the first and third coordinates. -/
abbrev overlapCoface₁ : D ⊗[B] D →ₐ[B] D ⊗[B] (D ⊗[B] D) :=
  TensorProduct.map (AlgHom.id B D) TensorProduct.includeRight

/-- Pull a double overlap to the first two coordinates. -/
abbrev overlapCoface₂ : D ⊗[B] D →ₐ[B] D ⊗[B] (D ⊗[B] D) :=
  TensorProduct.map (AlgHom.id B D) TensorProduct.includeLeft

variable (C : Type*) [CommRing C] [Algebra B C] [Module.Flat B D]

/-- The degree-zero kernel coboundary is the difference of the two actual inclusions. -/
theorem coverKernelInclusion_d₀ (w : D ⊗[B] RingHom.ker (algebraMap B C)) :
    (coverKernelInclusion B C D).lTensor D (Amitsur.d₀ B D _ w) =
      1 ⊗ₜ[B] coverKernelInclusion B C D w - coverKernelInclusion B C D w ⊗ₜ[B] 1 := by
  induction w using _root_.TensorProduct.inductionOn with
  | tmul d b =>
    simp only [Amitsur.d₀_tmul, map_sub, LinearMap.lTensor_tmul, coverKernelInclusion_tmul]
    simp only [tmul_smul, smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy, tmul_add, add_tmul]; abel

/-- The degree-one kernel differential is the alternating sum on actual triple overlaps. -/
theorem coverKernelInclusion_d₁
    (z : D ⊗[B] (D ⊗[B] RingHom.ker (algebraMap B C))) :
    ((coverKernelInclusion B C D).lTensor D).lTensor D (Amitsur.d₁ B D _ z) =
      overlapCoface₀ B D ((coverKernelInclusion B C D).lTensor D z) -
        overlapCoface₁ B D ((coverKernelInclusion B C D).lTensor D z) +
        overlapCoface₂ B D ((coverKernelInclusion B C D).lTensor D z) := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul d z =>
    induction z using _root_.TensorProduct.inductionOn with
    | tmul e b =>
      simp only [Amitsur.d₁_tmul, map_add, map_sub, LinearMap.lTensor_tmul,
        coverKernelInclusion_tmul, overlapCoface₀, overlapCoface₁, overlapCoface₂,
        TensorProduct.includeRight_apply, TensorProduct.map_tmul, AlgHom.id_apply,
        TensorProduct.includeLeft_apply]
      simp only [tmul_smul, smul_tmul']
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]; abel
  | add x y hx hy => simp only [map_add, hx, hy]; abel

end Algebra
