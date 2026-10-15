/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentIdealContraction
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.LinearCombination

/-!
# Inverting a linear polynomial with nilpotent coefficient corrections

An invertible linear coefficient and a polynomial in a nilpotent ideal give
a bijection of the whole ring. This supplies actual incidence inverses.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.NilpotentPolynomialInverse
variable {R : Type*} [CommRing R] (I : Ideal R) (p : R[X])
  (hp : p ∈ I.map C)

include hp in
/-- A polynomial with coefficients in I improves every I-adic congruence. -/
theorem eval_sub_mem (n : ℕ) (x y : R) (hxy : x - y ∈ I ^ n) :
    p.eval x - p.eval y ∈ I ^ (n + 1) := by
  classical
  rw [eval_eq_sum, eval_eq_sum, Polynomial.sum, Polynomial.sum, ← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro k _
  rw [← mul_sub, pow_succ']
  apply Ideal.mul_mem_mul ((Ideal.mem_map_C_iff.mp hp) k)
  obtain ⟨z, hz⟩ := sub_dvd_pow_sub_pow x y k
  rw [hz]
  exact (I ^ n).mul_mem_right z hxy

variable (hI : IsNilpotent I) (a : R) (ha : IsUnit a) (b : R)

/-- The correction step divides only by the specified unit linear coefficient. -/
def correction (x : R) : R := ↑(ha.unit⁻¹) * (b - p.eval x)

include hp in
/-- The correction is a contraction in the nilpotent ideal filtration. -/
theorem correction_contracts (n : ℕ) (x y : R) (hxy : x - y ∈ I ^ n) :
    correction p a ha b x - correction p a ha b y ∈ I ^ (n + 1) := by
  have h := (I ^ (n + 1)).mul_mem_left (↑(ha.unit⁻¹))
    ((I ^ (n + 1)).neg_mem (eval_sub_mem I p hp n x y hxy))
  convert h using 1
  simp only [correction]
  ring

/-- Finite nilpotent iteration constructs the inverse image of any right hand side. -/
def inverse : R :=
  NilpotentIdealContraction.fixedPoint I hI (correction p a ha b)
    (correction_contracts I p hp a ha b)

/-- The inverse solves the original, untruncated polynomial equation. -/
theorem inverse_equation : a * inverse I p hp hI a ha b +
    p.eval (inverse I p hp hI a ha b) = b := by
  have h := NilpotentIdealContraction.fixedPoint_eq I hI (correction p a ha b)
    (correction_contracts I p hp a ha b)
  change ↑(ha.unit⁻¹) * (b - p.eval (inverse I p hp hI a ha b)) =
    inverse I p hp hI a ha b at h
  have hm := congrArg (fun z ↦ a * z) h
  rw [← mul_assoc, ha.mul_val_inv, one_mul] at hm
  linear_combination -hm

include hp hI ha in
/-- There is only one inverse image, without a residue-value restriction. -/
theorem solution_unique {x y : R} (hx : a * x + p.eval x = b)
    (hy : a * y + p.eval y = b) : x = y := by
  apply NilpotentIdealContraction.fixedPoint_unique I hI (correction p a ha b)
    (correction_contracts I p hp a ha b)
  · change ↑(ha.unit⁻¹) * (b - p.eval x) = x
    rw [← hx, add_sub_cancel_right, ← mul_assoc, ha.val_inv_mul, one_mul]
  · change ↑(ha.unit⁻¹) * (b - p.eval y) = y
    rw [← hy, add_sub_cancel_right, ← mul_assoc, ha.val_inv_mul, one_mul]

end FLT.Mazur.NilpotentPolynomialInverse
