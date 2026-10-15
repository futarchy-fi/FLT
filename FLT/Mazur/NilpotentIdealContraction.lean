/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Logic.Function.Iterate

/-!
# Finite fixed points over nilpotent ideals

A function that improves ideal-adic congruence by one power has a unique
fixed point. Iteration terminates algebraically at the nilpotence exponent.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NilpotentIdealContraction
variable {R : Type*} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
  (f : R → R)
  (hf : ∀ (n : ℕ) (x y : R), x - y ∈ I ^ n → f x - f y ∈ I ^ (n + 1))

include hf in
/-- Consecutive iterates agree to successively higher ideal-adic order. -/
theorem iterate_difference (n : ℕ) : f ((f^[n]) 0) - (f^[n]) 0 ∈ I ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using hf n (f ((f^[n]) 0)) ((f^[n]) 0) ih

include hI hf in
/-- Nilpotence supplies a fixed point after finitely many actual iterations. -/
theorem exists_fixedPoint : ∃ x : R, f x = x := by
  obtain ⟨N, hN⟩ := hI
  refine ⟨(f^[N]) 0, ?_⟩
  have h := iterate_difference I f hf N
  rw [hN] at h
  exact sub_eq_zero.mp h

include hI hf in
/-- Improvement of congruence makes the fixed point unique in the entire ring. -/
theorem fixedPoint_unique {x y : R} (hx : f x = x) (hy : f y = y) : x = y := by
  have h (n : ℕ) : x - y ∈ I ^ n := by
    induction n with
    | zero => simp
    | succ n ih => simpa only [hx, hy] using hf n x y ih
  obtain ⟨N, hN⟩ := hI
  have hz := h N
  rw [hN] at hz
  exact sub_eq_zero.mp hz

/-- The unique fixed point is constructed from finite iteration. -/
def fixedPoint : R := (exists_fixedPoint I hI f hf).choose

/-- The constructed point satisfies the original fixed-point equation. -/
theorem fixedPoint_eq : f (fixedPoint I hI f hf) = fixedPoint I hI f hf :=
  (exists_fixedPoint I hI f hf).choose_spec

end FLT.Mazur.NilpotentIdealContraction
