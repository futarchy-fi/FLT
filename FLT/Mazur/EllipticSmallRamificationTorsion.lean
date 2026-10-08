/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalPrimeExpansion
public import FLT.Mazur.EllipticLocalMultiplication
public import FLT.GroupScheme.RaynaudFiniteValuation

/-!
# No formal p-torsion below the absolute ramification threshold

Evaluation of the integral p-series gives p times the parameter times a unit,
plus a pth-power remainder. A nonzero p-torsion parameter would force its
(p-1)st power to divide p times a unit, contradicting the absolute order bound.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing RaynaudParameters

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  [IsAdicComplete (maximalIdeal A) A]

/-- Evaluate the p-divisible low terms without changing the original coefficient ring. -/
theorem infinityParameter_prime_unit_expansion (p : ℕ) [Fact p.Prime]
    (P : ellipticE1 A W) :
    ∃ (u : Aˣ) (r : A), infinityParameter A W (p • P) =
      p * infinityParameter A W P * u + infinityParameter A W P ^ p * r := by
  obtain ⟨g, h, he⟩ := FormalInfinity.multiplicationSeries_prime_expansion W p
  let ev := localSeriesEvaluation A (infinityParameter A W P) (infinityParameter_mem A W P)
  have ht0 := (residue_eq_zero_iff _).mpr (infinityParameter_mem A W P)
  have hu : IsUnit (1 + infinityParameter A W P * ev g) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    simp [ht0]
  refine ⟨hu.unit, ev h, ?_⟩
  have hh := congrArg ev he
  simp only [ev, map_add, map_mul, map_pow, localSeriesEvaluation_C,
    localSeriesEvaluation_X] at hh
  rw [infinityParameter_nsmul A W, hu.unit_spec]
  change ev (FormalInfinity.multiplicationSeries W p) = _
  linear_combination hh

variable [IsDiscreteValuationRing A]

/-- A nonzero formal p-torsion point requires absolute order at least p-1. -/
theorem ellipticE1_prime_torsion_order_bound (p : ℕ) [Fact p.Prime]
    (hp0 : (p : A) ≠ 0) (P : ellipticE1 A W) (hP : P ≠ 0) (hpP : p • P = 0) :
    p - 1 ≤ order (p : A) := by
  have ht : infinityParameter A W P ≠ 0 :=
    mt (infinityParameter_eq_zero_iff A W P).mp hP
  have ho : 1 ≤ order (infinityParameter A W P) := by
    have hn : ¬ IsUnit (infinityParameter A W P) :=
      mem_nonunits_iff.mp (infinityParameter_mem A W P)
    have hz := mt (order_eq_zero_iff ht).mp hn
    omega
  obtain ⟨u, r, he⟩ := infinityParameter_prime_unit_expansion A W p P
  rw [hpP, infinityParameter_zero] at he
  have hm : infinityParameter A W P ^ (p - 1) * (-r) = (p : A) * u := by
    apply mul_left_cancel₀ ht
    have hpow : infinityParameter A W P ^ p =
        infinityParameter A W P * infinityParameter A W P ^ (p - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
    rw [hpow] at he
    linear_combination he
  have hd := (order_le_of_product hp0 u hm).2
  rw [order_pow ht] at hd
  exact (Nat.le_mul_of_pos_right _ ho).trans hd

/-- The actual formal kernel has no p-torsion under the strict ramification bound. -/
theorem ellipticE1_prime_nsmul_eq_zero_iff_small_ramification (p : ℕ) [Fact p.Prime]
    (hp0 : (p : A) ≠ 0) (he : order (p : A) < p - 1) (P : ellipticE1 A W) :
    p • P = 0 ↔ P = 0 := by
  constructor
  · intro hpP
    by_contra hP
    exact (not_le_of_gt he) (ellipticE1_prime_torsion_order_bound A W p hp0 P hP hpP)
  · rintro rfl
    exact nsmul_zero _

/-- The same bound excludes every p-primary torsion point in the actual formal kernel. -/
theorem ellipticE1_prime_pow_nsmul_eq_zero_iff_small_ramification
    (p k : ℕ) [Fact p.Prime] (hp0 : (p : A) ≠ 0) (he : order (p : A) < p - 1)
    (P : ellipticE1 A W) : p ^ k • P = 0 ↔ P = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_nsmul,
      ellipticE1_prime_nsmul_eq_zero_iff_small_ramification A W p hp0 he, ih]

end FLT.Mazur
