/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfDifferentials

/-! # Convolution powers across a square-zero ideal -/

@[expose] public noncomputable section
open WithConv
namespace HopfAlgebra
variable {R A B : Type*} [CommRing R] [AddCommGroup A] [Module R A]
  [Coalgebra R A] [Coalgebra.IsCocomm R A] [CommRing B] [Algebra R B]

omit [Coalgebra.IsCocomm R A] in
/-- Maps into a square-zero ideal have square-zero convolution square. -/
theorem conv_sq_eq_zero_of_mem (J : Ideal B) (hJ : J ^ 2 = ⊥)
    (d : A →ₗ[R] B) (hd : ∀ a, d a ∈ J) : toConv d ^ 2 = 0 := by
  rw [pow_two]
  apply WithConv.ext
  ext a
  rw [(Coalgebra.Repr.arbitrary R a).convMul_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have h := Ideal.mul_mem_mul (hd ((Coalgebra.Repr.arbitrary R a).left i))
    (hd ((Coalgebra.Repr.arbitrary R a).right i))
  rw [← pow_two, hJ] at h
  exact h

/-- Square-zero perturbations annihilated by N do not change the N-th power. -/
theorem pow_eq_of_sq_zero_sub {T : Type*} [CommRing T] (f g : T) (N : ℕ)
    (hsq : (f - g) ^ 2 = 0) (hN : N • (f - g) = 0) : f ^ N = g ^ N := by
  cases N with
  | zero => simp
  | succ n =>
    have h := pow_add_of_sq_zero g (f - g) hsq n
    rw [add_sub_cancel, ← mul_smul_comm, hN, mul_zero, add_zero] at h
    exact h

/-- Congruent linear maps have identical convolution powers if N kills the square-zero ideal. -/
theorem convPow_eq_of_sub_mem (J : Ideal B) (hJ : J ^ 2 = ⊥) (N : ℕ)
    (hN : ∀ b ∈ J, N • b = 0) (f g : A →ₗ[R] B)
    (hfg : ∀ a, f a - g a ∈ J) : toConv f ^ N = toConv g ^ N := by
  apply pow_eq_of_sq_zero_sub
  · exact conv_sq_eq_zero_of_mem J hJ (f - g) hfg
  · apply WithConv.ext
    ext a
    exact hN _ (hfg a)

end HopfAlgebra
