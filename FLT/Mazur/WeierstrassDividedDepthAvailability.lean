/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthData

/-!
# Construct every earlier depth from actual terminal coefficient divisibility

A single available terminal datum supplies all intermediate data required by
the finite model. Existence is exactly divisibility of the three original
coefficients; no smoothness or model existence is stored in the datum.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R} {k l : ℕ}

/-- Coefficient divisibility constructs actual data at a specified depth. -/
def Data.ofDivisibility (h3 : π ^ k ∣ W.a₃) (h4 : π ^ k ∣ W.a₄)
    (h6 : (π ^ k) ^ 2 ∣ W.a₆) : Data W π k where
  b3 := h3.choose
  b4 := h4.choose
  b6 := h6.choose
  factor3 := h3.choose_spec
  factor4 := h4.choose_spec
  factor6 := h6.choose_spec

/-- Actual depth availability is equivalent to three original coefficient divisibilities. -/
theorem data_nonempty_iff : Nonempty (Data W π k) ↔
    π ^ k ∣ W.a₃ ∧ π ^ k ∣ W.a₄ ∧ (π ^ k) ^ 2 ∣ W.a₆ := by
  constructor
  · rintro ⟨d⟩
    exact ⟨⟨d.b3, d.factor3⟩, ⟨d.b4, d.factor4⟩, ⟨d.b6, d.factor6⟩⟩
  · rintro ⟨h3, h4, h6⟩
    exact ⟨Data.ofDivisibility h3 h4 h6⟩

/-- A deeper datum constructs an earlier one by multiplying the remaining scale. -/
def Data.truncate (e : Data W π l) (hkl : k ≤ l) : Data W π k where
  b3 := π ^ (l - k) * e.b3
  b4 := π ^ (l - k) * e.b4
  b6 := (π ^ (l - k)) ^ 2 * e.b6
  factor3 := by rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hkl]; exact e.factor3
  factor4 := by rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hkl]; exact e.factor4
  factor6 := by
    rw [← mul_assoc, ← mul_pow, ← pow_add, Nat.add_sub_of_le hkl]
    exact e.factor6

/-- A terminal datum supplies every member of the actual finite depth family. -/
def Data.finiteFamily {start n : ℕ} (e : Data W π (start + n))
    (i : Fin (n + 1)) : Data W π (start + i.val) :=
  e.truncate (Nat.add_le_add_left (Nat.le_of_lt_succ i.isLt) start)

variable [IsDomain R] (hπ : π ≠ 0)
include hπ

/-- At a fixed depth the original coefficients uniquely determine all quotient data. -/
theorem Data.eq_of_depth (d e : Data W π k) : d = e := by
  have h3 : d.b3 = e.b3 := mul_left_cancel₀ (pow_ne_zero k hπ)
    (d.factor3.symm.trans e.factor3)
  have h4 : d.b4 = e.b4 := mul_left_cancel₀ (pow_ne_zero k hπ)
    (d.factor4.symm.trans e.factor4)
  have h6 : d.b6 = e.b6 := mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero k hπ))
    (d.factor6.symm.trans e.factor6)
  cases d
  cases e
  simp_all

/-- The constructed finite family's terminal member is the original datum. -/
theorem Data.finiteFamily_last {start n : ℕ} (e : Data W π (start + n)) :
    e.finiteFamily ⟨n, Nat.lt_succ_self n⟩ = e := Data.eq_of_depth hπ _ _

/-- Truncating terminal data recovers any previously chosen datum at the same depth. -/
theorem Data.truncate_eq (d : Data W π k) (e : Data W π l) (hkl : k ≤ l) :
    e.truncate hkl = d := Data.eq_of_depth hπ _ _

end FLT.Mazur.WeierstrassDividedDepth
