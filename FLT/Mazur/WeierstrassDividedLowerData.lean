/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthData

/-!
# Extending divided coefficient data to earlier depths

Multiplication by the missing uniformizer powers constructs the earlier data.
Over a domain these are the unique quotients of the original coefficients.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R} {k l : ℕ}

/-- Restore the uniformizer powers removed between two depths. -/
def Data.lower (d : Data W π l) (h : k ≤ l) : Data W π k where
  b3 := π ^ (l - k) * d.b3
  b4 := π ^ (l - k) * d.b4
  b6 := (π ^ (l - k)) ^ 2 * d.b6
  factor3 := by rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le h]; exact d.factor3
  factor4 := by rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le h]; exact d.factor4
  factor6 := by
    rw [← mul_assoc, ← mul_pow, ← pow_add, Nat.add_sub_of_le h]
    exact d.factor6

/-- Lowering to the same depth preserves the actual coefficients and their proofs. -/
@[simp] theorem Data.lower_self (d : Data W π k) : d.lower le_rfl = d := by
  cases d
  simp [Data.lower]

variable [IsDomain R] (hπ : π ≠ 0)

include hπ in
/-- Division of the original coefficients by a nonzero uniformizer power is unique. -/
theorem Data.unique (d e : Data W π k) : d = e := by
  have h3 : d.b3 = e.b3 := mul_left_cancel₀ (pow_ne_zero k hπ)
    (d.factor3.symm.trans e.factor3)
  have h4 : d.b4 = e.b4 := mul_left_cancel₀ (pow_ne_zero k hπ)
    (d.factor4.symm.trans e.factor4)
  have h6 : d.b6 = e.b6 := mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero k hπ))
    (d.factor6.symm.trans e.factor6)
  cases d
  cases e
  cases h3
  cases h4
  cases h6
  rfl

include hπ in
/-- Lowering agrees with any already supplied datum at the earlier depth. -/
theorem Data.lower_eq (d : Data W π l) (h : k ≤ l) (e : Data W π k) :
    d.lower h = e := Data.unique hπ _ _

include hπ in
/-- Successive extensions to earlier depths are independent of the intermediate depth. -/
theorem Data.lower_trans {j : ℕ} (d : Data W π l) (h : k ≤ l) (g : j ≤ k) :
    (d.lower h).lower g = d.lower (g.trans h) := Data.unique hπ _ _

end FLT.Mazur.WeierstrassDividedDepth
