/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.MappedRankTwoCharpoly
public import FLT.Deformations.RepresentationTheory.TameSpectrumDigits

/-!
# Determinant selection for mapped binary characteristic polynomials

These algebraic lemmas consume binary factors explicitly. Arithmetic wrappers
must derive those factors and the generator from the original flat model.
-/

@[expose] public noncomputable section
namespace Representation
open Polynomial

variable {k F V : Type*} [Field k] [Field F] [AddCommGroup V] [Module k V]
  [Module.Finite k V] (T : Module.End k V) (f : k →+* F)
  (hV : Module.finrank k V = 2) {p a b : ℕ} {z : Fˣ}

include hV in
/-- The mapped ordinary binary spectrum is selected by the original determinant. -/
theorem ordinary_map_charpoly_of_digits (hp : 3 < p) (hz : orderOf z = p - 1)
    (ha : a ≤ 1) (hb : b ≤ 1) (hd : f T.det = (z : F))
    (hf : T.charpoly.map f = (X - C ((z : F) ^ a)) * (X - C ((z : F) ^ b))) :
    T.charpoly.map f = (X - C 1) * (X - C (z : F)) := by
  have hd' : z ^ a * z ^ b = z := by
    apply Units.ext
    exact ((T.trace_det_of_map_charpoly_factors f hV _ _ hf).2.symm.trans hd)
  rcases ordinary_digits hp hz ha hb hd' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa using hf
  · simpa only [pow_zero, pow_one, mul_comm] using hf

/-- Frobenius exchanges the two binary exponents at a full niveau-two generator. -/
theorem niveau_two_binary_frobenius (hp : 1 < p) (hz : orderOf z = p * p - 1) :
    (z ^ (p * a + b)) ^ p = z ^ (a + p * b) := by
  have hzpp : z ^ (p * p) = z := by
    have h : z ^ (p * p - 1) = 1 := hz ▸ pow_orderOf_eq_one z
    calc
      z ^ (p * p) = z ^ (p * p - 1 + 1) := by
        rw [Nat.sub_add_cancel (by nlinarith : 1 ≤ p * p)]
      _ = z := by rw [pow_succ, h, one_mul]
  calc
    (z ^ (p * a + b)) ^ p = (z ^ (p * p)) ^ a * z ^ (p * b) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring
    _ = z ^ (a + p * b) := by rw [hzpp, pow_add]

include hV in
/-- The mapped niveau-two binary spectrum is selected by the original determinant. -/
theorem niveau_two_map_charpoly_of_digits (hp : 3 < p) (hz : orderOf z = p * p - 1)
    (ha : a ≤ 1) (hb : b ≤ 1) (hd : f T.det = ((z ^ (p + 1) : Fˣ) : F))
    (hf : T.charpoly.map f = (X - C ((z : F) ^ (p * a + b))) *
      (X - C (((z : F) ^ (p * a + b)) ^ p))) :
    T.charpoly.map f = (X - C (z : F)) * (X - C ((z ^ p : Fˣ) : F)) := by
  have he := niveau_two_binary_frobenius (a := a) (b := b) (by omega : 1 < p) hz
  have heF := congrArg (fun u : Fˣ ↦ (u : F)) he
  simp only [Units.val_pow_eq_pow_val] at heF
  rw [heF] at hf
  have hd' : z ^ (a + p * b) * z ^ (p * a + b) = z ^ (p + 1) := by
    apply Units.ext
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val, mul_comm] using
      ((T.trace_det_of_map_charpoly_factors f hV _ _ hf).2.symm.trans hd)
  rcases niveau_two_digits hp hz ha hb hd' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa using hf
  · simpa only [mul_one, add_zero, mul_zero, zero_add, pow_one,
      Units.val_pow_eq_pow_val, mul_comm] using hf

end Representation
