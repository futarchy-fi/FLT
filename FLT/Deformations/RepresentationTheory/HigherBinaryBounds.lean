/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.TameSpectrumDigits
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Bounds on higher binary weights

The full higher-niveau generator cannot satisfy the trace-zero quadratic
relation for a binary weight when p > 3. No Frobenius orbit bound is assumed.
-/

@[expose] public section
namespace Representation

/-- Reverse Frobenius indexing has the same geometric sum. -/
theorem reverse_power_sum (p r : ℕ) :
    (∑ i ∈ Finset.range r, p ^ (r - 1 - i)) = ∑ i ∈ Finset.range r, p ^ i := by
  exact Finset.sum_range_reflect (fun i ↦ p ^ i) r

/-- A binary cycle weight lies between zero and the cyclotomic norm exponent. -/
theorem higher_binary_weight_le (p : ℕ) (r : ℕ+) (d : Fin r → ℕ)
    (hd : ∀ i, d i ≤ 1) :
    (∑ i ∈ Finset.range (r : ℕ),
      d ⟨i % r, Nat.mod_lt _ r.pos⟩ * p ^ ((r : ℕ) - 1 - i)) ≤
      ∑ i ∈ Finset.range (r : ℕ), p ^ i := by
  rw [← reverse_power_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (Nat.mul_le_mul_right _ (hd _)).trans_eq (one_mul _)

/-- A short interval of exponents contains no negative of its central generator power. -/
theorem pow_ne_neg_of_short_interval {k : Type*} [Field k] {z : kˣ} {m S N : ℕ}
    (hchar : (2 : k) ≠ 0) (hz : orderOf z = N) (hN : 2 * S < N) (hm : m ≤ S) :
    (z : k) ^ (2 * m) ≠ -((z : k) ^ S) := by
  intro h
  have hu : z ^ (2 * m) = -(z ^ S) := Units.ext h
  have hs : z ^ (4 * m) = z ^ (2 * S) := by
    have hh := congrArg (fun u : kˣ ↦ u ^ 2) hu
    simpa only [neg_sq, ← pow_mul, show 2 * m * 2 = 4 * m by omega,
      Nat.mul_comm S 2] using hh
  have hi : Function.Injective (fun n : Fin N ↦ z ^ (n : ℕ)) := by
    rw [← hz]
    intro a b hab
    exact Fin.ext (pow_injOn_Iio_orderOf a.isLt b.isLt hab)
  by_cases hle : 2 * m ≤ S
  · have hmul : z ^ (2 * (S - 2 * m)) = 1 := by
      apply mul_left_cancel (a := z ^ (4 * m))
      rw [← pow_add, mul_one]
      convert hs.symm using 1; congr 1; omega
    have he : 2 * (S - 2 * m) = 0 := by
      have hh := hi (a₁ := ⟨2 * (S - 2 * m), by omega⟩) (a₂ := ⟨0, by omega⟩)
        (by simpa using hmul)
      exact congrArg Fin.val hh
    have heq : 2 * m = S := by omega
    rw [heq] at h
    have hn : (z : k) ^ S ≠ 0 := pow_ne_zero _ z.ne_zero
    exact hchar (by
      have hh : (2 : k) * (z : k) ^ S = 0 := by linear_combination h
      exact (mul_eq_zero.mp hh).resolve_right hn)
  · have hmul : z ^ (2 * (2 * m - S)) = 1 := by
      apply mul_left_cancel (a := z ^ (2 * S))
      rw [← pow_add, mul_one]
      convert hs using 1; congr 1; omega
    have he : 2 * (2 * m - S) = 0 := by
      have hh := hi (a₁ := ⟨2 * (2 * m - S), by omega⟩) (a₂ := ⟨0, by omega⟩)
        (by simpa using hmul)
      exact congrArg Fin.val hh
    omega

/-- Actual binary weights exclude the trace-zero quadratic relation at a full generator. -/
theorem higher_binary_square_ne_neg_norm {k : Type*} [Field k] {z : kˣ}
    {p : ℕ} (hp : 3 < p) (r : ℕ+) (d : Fin r → ℕ) (hd : ∀ i, d i ≤ 1)
    (hchar : (2 : k) ≠ 0) (hz : orderOf z = p ^ (r : ℕ) - 1) :
    (z : k) ^ (2 * (∑ i ∈ Finset.range (r : ℕ),
      d ⟨i % r, Nat.mod_lt _ r.pos⟩ * p ^ ((r : ℕ) - 1 - i))) ≠
        -((z : k) ^ (∑ i ∈ Finset.range (r : ℕ), p ^ i)) := by
  apply pow_ne_neg_of_short_interval hchar hz _ (higher_binary_weight_le p r d hd)
  have he := geom_sum_mul_of_one_le (by omega : 1 ≤ p) (r : ℕ)
  have hs : 0 < ∑ i ∈ Finset.range (r : ℕ), p ^ i :=
    Finset.sum_pos (fun i _ ↦ pow_pos (by omega) i) ⟨0, Finset.mem_range.mpr r.pos⟩
  have hp1 : 2 < p - 1 := by omega
  nlinarith

end Representation
