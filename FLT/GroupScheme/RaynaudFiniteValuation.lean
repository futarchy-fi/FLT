/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudDVRParameterValuation

/-!
# Finite valuations of nonzero DVR parameters

Natural-valued orders allow the existing integer scaling lemma to be
applied after nonvanishing has been established from the actual products.
-/

@[expose] public section
namespace RaynaudParameters
open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The finite natural valuation, used only with explicit nonvanishing proofs. -/
noncomputable def order (a : R) : ℕ := (addVal R a).toNat

/-- The natural order adds on nonzero products. -/
theorem order_mul {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    order (a * b) = order a + order b := by
  rw [order, addVal_mul, ENat.toNat_add
    (mt addVal_eq_top_iff.mp ha) (mt addVal_eq_top_iff.mp hb)]
  rfl

/-- Natural order of a nonzero power is its exponent times its order. -/
theorem order_pow {a : R} (ha : a ≠ 0) (n : ℕ) : order (a ^ n) = n * order a := by
  induction n with
  | zero => simp [order]
  | succ n ih => rw [pow_succ, order_mul (pow_ne_zero n ha) ha, ih, Nat.add_mul, one_mul]

/-- Natural order zero characterizes nonzero units. -/
theorem order_eq_zero_iff {a : R} (ha : a ≠ 0) : order a = 0 ↔ IsUnit a := by
  rw [order, ENat.toNat_eq_zero, or_iff_left (mt addVal_eq_top_iff.mp ha), addVal_eq_zero_iff]

/-- Multiplication by a unit leaves the order unchanged. -/
theorem order_mul_unit (a : R) (u : Rˣ) : order (a * u) = order a := by
  simp [order, addVal_eq_zero_of_unit]

/-- An actual complementary product proves nonvanishing and the ramification bound. -/
theorem order_le_of_product {a b t : R} (ht : t ≠ 0) (u : Rˣ) (h : a * b = t * u) :
    a ≠ 0 ∧ order a ≤ order t := by
  have hab : a * b ≠ 0 := h ▸ mul_ne_zero ht u.ne_zero
  have ha := (mul_ne_zero_iff.mp hab).1
  have hb := (mul_ne_zero_iff.mp hab).2
  have hv := congrArg order h
  rw [order_mul ha hb, order_mul_unit] at hv
  exact ⟨ha, by omega⟩

end RaynaudParameters
