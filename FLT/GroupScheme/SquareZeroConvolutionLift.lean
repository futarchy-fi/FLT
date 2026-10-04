/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ConvolutionTensorPower
public import FLT.GroupScheme.SquareZeroConvolution

/-! # Algebra-valued convolution lifts across square-zero ideals -/

@[expose] public noncomputable section
open scoped TensorProduct
open WithConv
namespace HopfAlgebra
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Bialgebra R A] [Coalgebra.IsCocomm R A] [Algebra R B]
  (J : Ideal B) (hJ : J ^ 2 = ⊥) (N : ℕ) (hN : ∀ b ∈ J, N • b = 0)
  (f : A →ₗ[R] B)
include hJ hN

/-- A multiplicative defect in J vanishes after the N-th convolution power. -/
theorem convPow_map_mul_of_defect_mem (hmul : ∀ a b, f (a * b) - f a * f b ∈ J)
    (a b : A) : (toConv f ^ N) (a * b) = (toConv f ^ N) a * (toConv f ^ N) b := by
  have hdef (t : A ⊗[R] A) :
      (f.comp (LinearMap.mul' R A) - convolutionTensorSquare f) t ∈ J := by
    induction t using TensorProduct.inductionOn with
    | tmul a b => exact hmul a b
    | add x y hx hy => simpa only [map_add] using J.add_mem hx hy
  have he := convPow_eq_of_sub_mem J hJ N hN
    (f.comp (LinearMap.mul' R A)) (convolutionTensorSquare f) hdef
  have h := congrArg (fun g : WithConv (A ⊗[R] A →ₗ[R] B) ↦ g (a ⊗ₜ[R] b)) he
  rw [← convPow_comp_mul, ← convolutionTensorSquare_pow] at h
  exact h

omit [Coalgebra.IsCocomm R A] in
/-- A unit defect in J also vanishes after the N-th convolution power. -/
theorem convPow_map_one_of_defect_mem (hone : f 1 - 1 ∈ J) : (toConv f ^ N) 1 = 1 := by
  rw [convPow_apply_one]
  have hsq : (f 1 - 1) ^ 2 = 0 := by
    have h := Ideal.mul_mem_mul hone hone
    rw [← pow_two, hJ] at h
    simpa only [pow_two, Ideal.mem_bot] using h
  simpa using pow_eq_of_sq_zero_sub (f 1) 1 N hsq (hN _ hone)

/-- Taking a convolution power turns an approximate algebra point into an actual point. -/
def squareZeroConvolutionLift (hone : f 1 - 1 ∈ J)
    (hmul : ∀ a b, f (a * b) - f a * f b ∈ J) : A →ₐ[R] B :=
  AlgHom.ofLinearMap (toConv f ^ N).ofConv
    (convPow_map_one_of_defect_mem J hJ N hN f hone)
    (convPow_map_mul_of_defect_mem J hJ N hN f hmul)

/-- The lift uses the original N-th convolution power. -/
theorem squareZeroConvolutionLift_apply (hone : f 1 - 1 ∈ J)
    (hmul : ∀ a b, f (a * b) - f a * f b ∈ J) (a : A) :
    squareZeroConvolutionLift J hJ N hN f hone hmul a = (toConv f ^ N) a := rfl

end HopfAlgebra
