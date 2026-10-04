/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleRationalCartierRoots

/-! # The chosen complex cyclotomic roots in the original algebraic closure -/

@[expose] public noncomputable section
open PadicHodgeTheory Polynomial
attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
namespace ThreeAdicPlan
variable (p : ℕ) [Fact p.Prime]
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)

/-- Each chosen complex root lies in the image of the fixed original algebraic closure. -/
theorem rationalCyclotomicRoot_exists (n : ℕ) :
    ∃ a : AlgebraicClosure K,
      rationalPlaceComplexMap p a = ((complexCyclotomicSequence p).val n : ℂ_[p]) := by
  let f : (AlgebraicClosure K)[X] := X ^ (p ^ n) - 1
  apply (IsAlgClosed.splits f).mem_range_of_isRoot
  · exact X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) 1
  · change (f.map (rationalPlaceComplexMap p)).eval _ = 0
    simp only [f, Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one,
      eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero]
    exact congrArg Subtype.val (complexCyclotomicSequence_primitive p n).pow_eq_one

/-- The unique preimage of the fixed complex cyclotomic root. -/
def rationalCyclotomicRoot (n : ℕ) : AlgebraicClosure K :=
  (rationalCyclotomicRoot_exists p n).choose

@[simp] theorem rationalCyclotomicRoot_map (n : ℕ) :
    rationalPlaceComplexMap p (rationalCyclotomicRoot p n) =
      ((complexCyclotomicSequence p).val n : ℂ_[p]) :=
  (rationalCyclotomicRoot_exists p n).choose_spec

/-- The transported root has the original p-power torsion relation. -/
theorem rationalCyclotomicRoot_pow (n : ℕ) : rationalCyclotomicRoot p n ^ (p ^ n) = 1 := by
  apply (rationalPlaceComplexMap p).injective
  rw [map_pow, rationalCyclotomicRoot_map, map_one]
  exact congrArg Subtype.val (complexCyclotomicSequence_primitive p n).pow_eq_one

/-- The transported roots retain all ordered transition relations. -/
theorem rationalCyclotomicRoot_transition {m n : ℕ} (h : m ≤ n) :
    rationalCyclotomicRoot p n ^ (p ^ (n - m)) = rationalCyclotomicRoot p m := by
  apply (rationalPlaceComplexMap p).injective
  rw [map_pow, rationalCyclotomicRoot_map, rationalCyclotomicRoot_map]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.add_sub_cancel_left]
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', pow_mul]
    change ((complexCyclotomicSequence p).val (m + d + 1) ^ p : ℂ_[p]) ^ (p ^ d) = _
    rw [← SubmonoidClass.coe_pow, (complexCyclotomicSequence p).property]
    exact ih (Nat.le_add_right _ _)

/-- A unit-valued version of the same actual root. -/
def rationalCyclotomicUnit (n : ℕ) : (AlgebraicClosure K)ˣ :=
  Units.mk0 (rationalCyclotomicRoot p n) (by
    intro hz
    have h := rationalCyclotomicRoot_pow p n
    rw [hz, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)] at h
    exact zero_ne_one h)

/-- The unit-valued roots have the same exponent. -/
theorem rationalCyclotomicUnit_pow (n : ℕ) : rationalCyclotomicUnit p n ^ (p ^ n) = 1 := by
  apply Units.ext
  exact rationalCyclotomicRoot_pow p n

/-- The unit-valued roots retain the ordered transitions. -/
theorem rationalCyclotomicUnit_transition {m n : ℕ} (h : m ≤ n) :
    rationalCyclotomicUnit p n ^ (p ^ (n - m)) = rationalCyclotomicUnit p m := by
  apply Units.ext
  exact rationalCyclotomicRoot_transition p h

end ThreeAdicPlan
