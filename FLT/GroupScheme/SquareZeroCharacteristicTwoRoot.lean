/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.SquareZeroConvolution
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.ZMod.Basic

/-! # A nonlifting quadratic root even when two kills the whole coefficient ring -/

@[expose] public noncomputable section
namespace HopfAlgebra.CharacteristicTwoRoot
open Polynomial

/-- The fourth-order truncated polynomial ring in characteristic two. -/
abbrev Coefficients := (ZMod 2)[X] ⧸ Ideal.span {(X : (ZMod 2)[X]) ^ 4}

/-- The nilpotent coordinate of the fourth-order truncated polynomial ring. -/
def parameter : Coefficients := Ideal.Quotient.mk _ X

/-- The parameter has fourth power zero. -/
theorem parameter_fourth : parameter ^ 4 = 0 := by
  rw [parameter, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Its square is nevertheless nonzero. -/
theorem parameter_square_ne_zero : parameter ^ 2 ≠ 0 := by
  rw [parameter, ← map_pow]
  intro h
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hc := (Polynomial.X_pow_dvd_iff.mp hd) 2 (by decide)
  norm_num at hc

/-- The second-order reduction of the fourth-order coefficient ring. -/
def reduction : Coefficients →+* (Coefficients ⧸ Ideal.span {parameter ^ 2}) :=
  Ideal.Quotient.mk _

/-- This coefficient map is surjective. -/
theorem reduction_surjective : Function.Surjective reduction := Ideal.Quotient.mk_surjective

/-- The reduction kernel has square zero. -/
theorem reduction_kernel_square : RingHom.ker reduction ^ 2 = ⊥ := by
  rw [reduction, Ideal.mk_ker, Ideal.span_singleton_pow, ← pow_mul]
  norm_num only [Nat.reduceMul, parameter_fourth, Ideal.span_singleton_eq_bot]

/-- Two kills every coefficient, not only the square-zero kernel. -/
theorem two_smul_coefficients (a : Coefficients) : 2 • a = 0 := by
  have h := congrArg (Ideal.Quotient.mk (Ideal.span {(X : (ZMod 2)[X]) ^ 4}))
    (CharP.cast_eq_zero (ZMod 2)[X] 2)
  rw [map_natCast, map_zero] at h
  rw [nsmul_eq_mul, h, zero_mul]

/-- The chosen lift of a quadratic root. -/
def liftedRoot : Coefficients := 1 + parameter

/-- Its square differs from one by exactly the nonzero infinitesimal parameter square. -/
theorem liftedRoot_square_sub_one : liftedRoot ^ 2 - 1 = parameter ^ 2 := by
  have h : (2 : Coefficients) * parameter = 0 := by
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using two_smul_coefficients parameter
  calc
    _ = 2 * parameter + parameter ^ 2 := by unfold liftedRoot; ring
    _ = _ := by rw [h, zero_add]

/-- The reduced value is a genuine quadratic root of unity. -/
theorem reducedRoot_square : reduction liftedRoot ^ 2 = 1 := by
  apply sub_eq_zero.mp
  rw [← map_pow, ← map_one reduction, ← map_sub, liftedRoot_square_sub_one]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- No lift of that same reduced root has square one. -/
theorem no_root_lift (a : Coefficients) (ha : reduction a = reduction liftedRoot) :
    a ^ 2 ≠ 1 := by
  have hm : a - liftedRoot ∈ RingHom.ker reduction := by
    change reduction (a - liftedRoot) = 0
    rw [map_sub, ha, sub_self]
  have hs : (a - liftedRoot) ^ 2 = 0 := by
    have h := Ideal.mul_mem_mul hm hm
    rw [← pow_two, reduction_kernel_square] at h
    simpa only [Ideal.mem_bot, pow_two] using h
  have he := HopfAlgebra.pow_eq_of_sq_zero_sub a liftedRoot 2 hs
    (two_smul_coefficients _)
  rw [he]
  intro h
  have hz := liftedRoot_square_sub_one
  rw [h, sub_self] at hz
  exact parameter_square_ne_zero hz.symm

end HopfAlgebra.CharacteristicTwoRoot
