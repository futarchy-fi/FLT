/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.RingTheory.Int.Basic

/-!
# Integral combinations that remove strict binomial degrees

For a non-prime-power frame size, construct integral coefficients whose
weighted strict binomial degrees sum to one. Applying these same coefficients
to degree-scaled lifts recovers the original coefficient in any additive group.
This is an integral construction and needs no degree to be a global unit.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BinomialBezoutCombination

/-- The finite positive strict subframe sizes. -/
abbrev Sizes (n : ℕ) := {m // m ∈ Finset.Icc 1 (n - 1)}

/-- Finite natural gcds agree with the gcds of their integer images. -/
theorem intCast_gcd (s : Finset ℕ) (d : ℕ → ℕ) :
    s.gcd (fun m ↦ (d m : ℤ)) = ((s.gcd d : ℕ) : ℤ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.gcd_insert, Finset.gcd_insert, ih]
    rfl

/-- Construct a finite integral combination of strict degrees equal to one. -/
theorem exists_coefficients (n : ℕ) (hn : 1 < n) (hp : ¬ IsPrimePow n) :
    ∃ a : Sizes n → ℤ, ∑ m, (n.choose m.val : ℤ) * a m = 1 := by
  obtain ⟨a, ha⟩ := Finset.gcd_eq_sum_mul (Finset.Icc 1 (n - 1))
    (fun m ↦ (n.choose m : ℤ))
  rw [intCast_gcd, Choose.gcd_choose_eq_one_of_not_isPrimePow hn hp, Nat.cast_one] at ha
  refine ⟨fun m ↦ a m.val, ?_⟩
  exact (Finset.sum_coe_sort (Finset.Icc 1 (n - 1))
    (fun m ↦ (n.choose m : ℤ) * a m)).trans ha.symm

/-- Chosen integral coefficients, independent of all chart lifts. -/
def coefficients (n : ℕ) (hn : 1 < n) (hp : ¬ IsPrimePow n) : Sizes n → ℤ :=
  (exists_coefficients n hn hp).choose

/-- The constructed coefficients remove the binomial degree exactly. -/
theorem coefficients_spec (n : ℕ) (hn : 1 < n) (hp : ¬ IsPrimePow n) :
    ∑ m, (n.choose m.val : ℤ) * coefficients n hn hp m = 1 :=
  (exists_coefficients n hn hp).choose_spec

/-- The integral combination of an actual family of additive lifts. -/
def combine {B : Type*} [AddCommGroup B] (n : ℕ) (hn : 1 < n)
    (hp : ¬ IsPrimePow n) (x : Sizes n → B) : B :=
  ∑ m, coefficients n hn hp m • x m

/-- Every additive map preserves the constructed combination. -/
theorem map_combine {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (n : ℕ) (hn : 1 < n) (hp : ¬ IsPrimePow n) (f : B →+ C) (x : Sizes n → B) :
    f (combine n hn hp x) = combine n hn hp (fun m ↦ f (x m)) := by
  simp only [combine, map_sum, map_zsmul]

/-- Independently chosen scaled lifts combine to one exact original lift. -/
theorem map_combine_scaled {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (n : ℕ) (hn : 1 < n) (hp : ¬ IsPrimePow n) (f : B →+ C)
    (x : Sizes n → B) (t : C) (hx : ∀ m, f (x m) = n.choose m.val • t) :
    f (combine n hn hp x) = t := by
  rw [map_combine]
  simp only [combine, hx, ← natCast_zsmul, smul_smul]
  rw [← Finset.sum_smul]
  have hh : ∑ m, coefficients n hn hp m * (n.choose m.val : ℤ) = 1 := by
    simpa only [mul_comm] using coefficients_spec n hn hp
  rw [hh, one_smul]

end FLT.Mazur.BinomialBezoutCombination
