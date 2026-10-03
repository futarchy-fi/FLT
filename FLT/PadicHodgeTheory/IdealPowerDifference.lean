/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Ring.GeomSum

/-! # Ideal bounds on iterated power differences -/

@[expose] public section
namespace PadicHodgeTheory
variable {R : Type*} [CommRing R]

/-- A power difference gains an ideal power when its exponent belongs to the ideal. -/
theorem ideal_pow_sub_pow_step (J : Ideal R) {p s : ℕ} (hp : (p : R) ∈ J)
    (hs : 1 ≤ s) {x y : R} (hxy : x - y ∈ J ^ s) :
    x ^ p - y ^ p ∈ J ^ (s + 1) := by
  have he : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y :=
    Ideal.Quotient.eq.mpr (Ideal.pow_le_self (by omega : s ≠ 0) hxy)
  have hg : (∑ i ∈ Finset.range p, x ^ i * y ^ (p - 1 - i)) ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp only [map_sum, map_mul, map_pow, he, geom_sum₂_self]
    rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem.mpr hp,
      zero_mul]
  rw [← geom_sum₂_mul, pow_succ]
  exact Ideal.mul_mem_mul_rev hxy hg

/-- After n iterations the difference lies in the (n+1)-st ideal power. -/
theorem ideal_pow_iterated_sub_mem (J : Ideal R) {p : ℕ} (hp : (p : R) ∈ J)
    {x y : R} (hxy : x - y ∈ J) (n : ℕ) :
    x ^ (p ^ n) - y ^ (p ^ n) ∈ J ^ (n + 1) := by
  induction n with
  | zero => simpa using hxy
  | succ n ih =>
    simpa only [pow_succ p, pow_mul] using
      ideal_pow_sub_pow_step J hp (Nat.succ_le_succ (Nat.zero_le n)) ih

/-- Splitting the mixed ideal yields simultaneous parameter and quotient precision. -/
theorem ideal_pow_iterated_sub_mem_sup (I : Ideal R) (p k r n : ℕ)
    (hn : k + r ≤ n + 1) {x y : R} (hxy : x - y ∈ I) :
    x ^ (p ^ n) - y ^ (p ^ n) ∈ Ideal.span {(p : R)} ^ k ⊔ I ^ r := by
  apply (Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(p : R)}) (J := I)
    (n := k) (m := r))
  apply Ideal.pow_le_pow_right hn
  exact ideal_pow_iterated_sub_mem _
    (show (p : R) ∈ Ideal.span {(p : R)} ⊔ I from
      (show Ideal.span {(p : R)} ≤ Ideal.span {(p : R)} ⊔ I from le_sup_left)
        (Ideal.subset_span (Set.mem_singleton _)))
    ((show I ≤ Ideal.span {(p : R)} ⊔ I from le_sup_right) hxy) n

end PadicHodgeTheory
