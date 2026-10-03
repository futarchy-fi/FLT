/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudMixedPowerConstant
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Factorial.NatCast

/-!
# Digit weights and their binomial products

Expand base-p digits into repeated weights 1,p,p²,…. Lucas's theorem
reduces their binomial product to the product of the digit factorials.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CharacterAverage

/-- A digit vector, least significant first, expanded into individual weights. -/
def digitWeights (p : ℕ) : List ℕ → List ℕ
  | [] => []
  | d :: ds => List.replicate d 1 ++ (digitWeights p ds).map (p * ·)

/-- Scaling a list scales its sum. -/
theorem sum_scale_weights (p : ℕ) (ks : List ℕ) :
    (ks.map (p * ·)).sum = p * ks.sum := by
  induction ks with
  | nil => simp
  | cons k ks ih => simp [ih, Nat.mul_add]

/-- The sum of digit weights is the number represented by the digits. -/
theorem digitWeights_sum (p : ℕ) (ds : List ℕ) :
    (digitWeights p ds).sum = Nat.ofDigits p ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [digitWeights, List.sum_append, List.sum_replicate,
      nsmul_eq_mul, Nat.cast_id, mul_one,
      sum_scale_weights, ih, Nat.ofDigits_cons]

/-- All expanded digit weights are positive in a positive base. -/
theorem digitWeights_pos (p : ℕ) (hp : 0 < p) (ds : List ℕ) :
    ∀ k ∈ digitWeights p ds, 0 < k := by
  induction ds with
  | nil => simp [digitWeights]
  | cons d ds ih =>
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · have : k = 1 := (List.mem_replicate.mp hk).2
      omega
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
      exact Nat.mul_pos hp (ih j hj)

variable {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- Multiplying every weight and the remainder by p preserves the residue coefficient. -/
theorem weightCoefficient_scale (ks : List ℕ) (n : ℕ) :
    (weightCoefficient (ks.map (p * ·)) (p * n) : R) = (weightCoefficient ks n : R) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.map_cons, weightCoefficient, sum_scale_weights,
      ← Nat.mul_add, Nat.cast_mul, ih]
    congr 1
    exact CharP.natCast_eq_natCast' R p Choose.choose_mul_mul_modEq_choose_nat

/-- Removing d unit weights above p-divisible weights contributes d factorial. -/
theorem weightCoefficient_low_digit (d : ℕ) (ks : List ℕ) :
    (weightCoefficient (List.replicate d 1 ++ ks.map (p * ·)) 0 : R) =
      (d.factorial : R) * (weightCoefficient ks 0 : R) := by
  induction d with
  | zero => simpa [weightCoefficient] using weightCoefficient_scale (R := R) p ks 0
  | succ d ih =>
    simp only [List.replicate_succ, List.cons_append, weightCoefficient,
      Nat.choose_one_right, Nat.cast_mul, ih, List.sum_append, List.sum_replicate,
      nsmul_eq_mul, Nat.cast_id, mul_one, sum_scale_weights, Nat.cast_add,
      Nat.cast_mul, CharP.cast_eq_zero, zero_mul, add_zero, Nat.factorial_succ]
    ring

/-- The residue of the mixed digit binomial product is the product of digit factorials. -/
theorem weightCoefficient_digits (ds : List ℕ) :
    (weightCoefficient (digitWeights p ds) 0 : R) =
      ((ds.map Nat.factorial).prod : R) := by
  induction ds with
  | nil => simp [digitWeights, weightCoefficient]
  | cons d ds ih =>
    rw [digitWeights, weightCoefficient_low_digit, ih]
    simp

/-- Genuine base-p digits give an invertible mixed binomial coefficient. -/
theorem isUnit_weightCoefficient_digits (ds : List ℕ) (hds : ∀ d ∈ ds, d < p) :
    IsUnit (weightCoefficient (digitWeights p ds) 0 : R) := by
  rw [weightCoefficient_digits]
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul]
    exact ((IsUnit.natCast_factorial_iff_of_charP p).mpr (hds d (by simp))).mul
      (ih (fun j hj ↦ hds j (by simp [hj])))

end ThreeAdicPlan.CharacterAverage
