/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticLocalValuation

/-!
# Strict depth and primary torsion in the local elliptic kernel

The quadratic estimate is sufficient at residue characteristic two once the
parameter is deeper than the scalar. At the boundary, one multiplication enters
that strict range. No odd-residue-characteristic hypothesis is used here.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
variable [IsAdicComplete (maximalIdeal A) A]

/-- A parameter at least as deep as a nonzero nonunit scalar becomes strictly deeper. -/
theorem infinityParameter_nsmul_valuation_lt (n : ℕ) (P : ellipticE1 A W)
    (hn0 : 0 < A.valuation (n : K)) (hn1 : A.valuation (n : K) < 1)
    (ht : A.valuation (infinityParameter A W P : K) ≤ A.valuation (n : K)) :
    A.valuation (infinityParameter A W (n • P) : K) < A.valuation (n : K) := by
  apply lt_of_le_of_lt (infinityParameter_nsmul_valuation_le A W n P)
  apply lt_of_le_of_lt (max_le (show _ ≤ A.valuation (n : K) ^ 2 from
    by simpa only [pow_two] using mul_le_mul le_rfl ht zero_le zero_le)
    (pow_le_pow_left₀ zero_le ht 2))
  simpa only [pow_two, mul_one] using mul_lt_mul_of_pos_left hn1 hn0

/-- Strict depth excludes torsion of every power of the scalar, including at two. -/
theorem ellipticE1_pow_nsmul_eq_zero_of_valuation_lt (n k : ℕ)
    (hn0 : 0 < A.valuation (n : K)) (hn1 : A.valuation (n : K) < 1)
    (P : ellipticE1 A W)
    (ht : A.valuation (infinityParameter A W P : K) < A.valuation (n : K))
    (hP : n ^ k • P = 0) : P = 0 := by
  induction k generalizing P with
  | zero => simpa using hP
  | succ k ih =>
    have hd := infinityParameter_nsmul_valuation_lt A W n P hn0 hn1 ht.le
    have hz : n ^ k • (n • P) = 0 := by simpa only [pow_succ', mul_nsmul] using hP
    exact ellipticE1_eq_zero_of_nsmul_eq_zero_of_valuation_lt A W n P ht (ih _ hd hz)

omit [IsAdicComplete (maximalIdeal A) A] in
/-- A generator of the maximal ideal bounds the valuation of every local parameter. -/
theorem infinityParameter_valuation_le_generator (n : ℕ)
    (hm : maximalIdeal A = Ideal.span {(n : A)}) (P : ellipticE1 A W) :
    A.valuation (infinityParameter A W P : K) ≤ A.valuation (n : K) := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (hm ▸ infinityParameter_mem A W P)
  rw [ha]
  push_cast
  rw [map_mul]
  exact mul_le_of_le_one_right' (A.valuation_le_one a)

/-- In the unramified case all primary torsion in E₁ is killed by the first scalar.
For n = 2 this retains the possible two-torsion instead of incorrectly excluding it. -/
theorem ellipticE1_nsmul_eq_zero_of_pow_nsmul_eq_zero_unramified (n k : ℕ)
    (hm : maximalIdeal A = Ideal.span {(n : A)}) (hn0 : (n : K) ≠ 0)
    (P : ellipticE1 A W) (hP : n ^ k • P = 0) : n • P = 0 := by
  have hnmem : (n : A) ∈ maximalIdeal A := hm ▸ Ideal.subset_span (by simp)
  have hn1 : A.valuation (n : K) < 1 := (A.valuation_lt_one_iff (n : A)).mp hnmem
  have hnpos : 0 < A.valuation (n : K) := (A.valuation.pos_iff).mpr hn0
  apply ellipticE1_pow_nsmul_eq_zero_of_valuation_lt A W n k hnpos hn1 (n • P)
    (infinityParameter_nsmul_valuation_lt A W n P hnpos hn1
      (infinityParameter_valuation_le_generator A W n hm P))
  rw [← mul_nsmul, mul_comm, mul_nsmul, hP, nsmul_zero]

end FLT.Mazur
