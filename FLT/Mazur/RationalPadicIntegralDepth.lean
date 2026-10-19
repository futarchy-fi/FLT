/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PadicValuationArithmetic

/-!
# Ideal depth and the original rational p-adic valuation

An exact maximal-ideal depth of an integral lift computes the valuation of
the original rational number. This converts local integral discriminant
statements into arithmetic statements about the actual rational equation.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing

/-- Exact depth of an integral rational coefficient is its ordinary rational valuation. -/
theorem rationalPadicIntegral_depth (q : ℕ) [Fact q.Prime]
    (x : ℚ) (y : padicIntegerSubring q)
    (hy : algebraMap (padicIntegerSubring q) ℚ_[q] y = algebraMap ℚ ℚ_[q] x)
    (n : ℕ) (hn : y ∈ maximalIdeal (padicIntegerSubring q) ^ n)
    (hs : y ∉ maximalIdeal (padicIntegerSubring q) ^ (n + 1)) :
    padicValRat q x = (n : ℤ) := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hs (Ideal.zero_mem _)
  rw [padicIntegerSubring_maximalIdeal, Ideal.span_singleton_pow] at hn hs
  have hlo : n ≤ PadicInt.valuation y :=
    (PadicInt.mem_span_pow_iff_le_valuation y hy0 n).mp hn
  have hhi : ¬ n + 1 ≤ PadicInt.valuation y :=
    fun hle ↦ hs ((PadicInt.mem_span_pow_iff_le_valuation y hy0 (n + 1)).mpr hle)
  have he : PadicInt.valuation y = n := by omega
  have hv := congrArg Padic.valuation hy
  change Padic.valuation (y : ℚ_[q]) = Padic.valuation (x : ℚ_[q]) at hv
  have hvy : Padic.valuation (y : ℚ_[q]) = (PadicInt.valuation y : ℤ) :=
    PadicInt.valuation_coe y
  rw [hvy, Padic.valuation_ratCast, he] at hv
  exact hv.symm

/-- A unit integral lift gives valuation zero for the original rational coefficient. -/
theorem rationalPadicIntegral_unit_valuation (q : ℕ) [Fact q.Prime]
    (x : ℚ) (y : padicIntegerSubring q)
    (hy : algebraMap (padicIntegerSubring q) ℚ_[q] y = algebraMap ℚ ℚ_[q] x)
    (hu : IsUnit y) : padicValRat q x = 0 := by
  have hm : y ∉ maximalIdeal (padicIntegerSubring q) := by
    simpa only [mem_maximalIdeal, mem_nonunits_iff, not_not] using hu
  exact rationalPadicIntegral_depth q x y hy 0 (by simp) (by simpa using hm)

end FLT.Mazur
