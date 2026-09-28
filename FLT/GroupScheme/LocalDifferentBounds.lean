/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalPointField
public import FLT.Mathlib.RingTheory.DifferentPowerBasis

/-!
# Local different bounds from annihilation of integral differentials

Membership of `3^k` in the different bounds its normalized exponent by `k`.
For a ring of integers equipped with an integral power basis, this membership
is equivalent to annihilation of its Kähler differentials. These statements
concern the full ring of integers, not the finite flat coordinate ring or
the image of an integral point; no such comparison is assumed here.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (L : Type*) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]

/-- Inclusion of nonzero integral ideals reverses their maximal-ideal orders. -/
theorem threeAdicIdealOrder_antitone {I J : Ideal (ThreeAdicIntegers L)}
    (hI : I ≠ ⊥) (h : I ≤ J) : threeAdicIdealOrder L J ≤ threeAdicIdealOrder L I := by
  classical
  have hJ : J ≠ ⊥ := ne_bot_of_le_ne_bot hI h
  exact Multiset.count_le_of_le _
    ((UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hJ hI).mp
      (Ideal.dvd_iff_le.mpr h))

/-- Normalized ideal order is also antitone away from the zero ideal. -/
theorem normalizedIdealOrder_antitone {I J : Ideal (ThreeAdicIntegers L)}
    (hI : I ≠ ⊥) (h : I ≤ J) : normalizedIdealOrder L J ≤ normalizedIdealOrder L I := by
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (threeAdicIdealOrder_antitone L hI h))
    (Nat.cast_nonneg _)

/-- Taking a power multiplies normalized ideal order by its exponent. -/
@[simp] theorem normalizedIdealOrder_pow (I : Ideal (ThreeAdicIntegers L)) (k : ℕ) :
    normalizedIdealOrder L (I ^ k) = k * normalizedIdealOrder L I := by
  simp [normalizedIdealOrder, mul_div_assoc]

/-- Containment of `3^k` in the different gives an upper bound for its exponent. -/
theorem normalizedDifferentExponent_le_of_three_pow_mem (k : ℕ)
    (hk : (3 : ThreeAdicIntegers L) ^ k ∈ differentIdeal ℤ_[3] (ThreeAdicIntegers L)) :
    normalizedDifferentExponent L ≤ k := by
  have : CharZero (ThreeAdicIntegers L) := Algebra.charZero_of_charZero ℤ_[3] _
  have hI : Ideal.span {(3 : ThreeAdicIntegers L) ^ k} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero _ (by norm_num)
  have h := normalizedIdealOrder_antitone L hI (Ideal.span_le.mpr (by simpa using hk))
  simpa only [normalizedDifferentExponent, ← Ideal.span_singleton_pow, normalizedIdealOrder_pow,
    normalizedIdealOrder_three, mul_one] using h

/-- In the monogenic case, an annihilating power of three bounds the different. -/
theorem normalizedDifferentExponent_le_of_kaehler_annihilation
    (pb : PowerBasis ℤ_[3] (ThreeAdicIntegers L)) (k : ℕ)
    (hk : ∀ ω : KaehlerDifferential ℤ_[3] (ThreeAdicIntegers L), (3 : ℤ_[3]) ^ k • ω = 0) :
    normalizedDifferentExponent L ≤ k := by
  apply normalizedDifferentExponent_le_of_three_pow_mem L k
  apply (pb.mem_differentIdeal_iff ℚ_[3] L _).mpr
  intro ω
  simpa only [← IsScalarTower.algebraMap_smul (ThreeAdicIntegers L), map_pow, map_ofNat]
    using hk ω

/-- Annihilation of integral differentials by three gives the strict Fontaine
numerical bound, provided an integral power basis is available. -/
theorem normalizedDifferentExponent_lt_three_halves_of_kaehler_annihilation
    (pb : PowerBasis ℤ_[3] (ThreeAdicIntegers L))
    (h : ∀ ω : KaehlerDifferential ℤ_[3] (ThreeAdicIntegers L), (3 : ℤ_[3]) • ω = 0) :
    normalizedDifferentExponent L < (3 / 2 : ℚ) := by
  have hle : normalizedDifferentExponent L ≤ 1 :=
    normalizedDifferentExponent_le_of_kaehler_annihilation L pb 1 (by simpa using h)
  linarith

end ThreeAdicPlan
