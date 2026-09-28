/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalDifferentBounds
public import FLT.GroupScheme.LocalIntegralPowerBasis
public import FLT.GroupScheme.PointImageConductor

/-!
# The different and the conductor of an integral point image

For an integral point of a finite flat model killed by three, three times
the conductor of its image lies in the different of the target local field.
Consequently a nonzero conductor gives the bound `v(D) ≤ 1 + v(C)`.
This is a transfer theorem; existence of a conductor of order below `1/2`
is not asserted, and the full Fontaine bound remains separate.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (L : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]

/-- Ideal order is additive on products of nonzero integral ideals. -/
theorem threeAdicIdealOrder_mul {I J : Ideal (ThreeAdicIntegers L)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    threeAdicIdealOrder L (I * J) = threeAdicIdealOrder L I + threeAdicIdealOrder L J := by
  classical
  simp only [threeAdicIdealOrder,
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.count_add]

/-- Normalized ideal order is additive on products of nonzero integral ideals. -/
theorem normalizedIdealOrder_mul {I J : Ideal (ThreeAdicIntegers L)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    normalizedIdealOrder L (I * J) = normalizedIdealOrder L I + normalizedIdealOrder L J := by
  simp only [normalizedIdealOrder, threeAdicIdealOrder_mul L hI hJ, Nat.cast_add, add_div]

/-- The conductor of every integral point image, multiplied by the killing
integer of the model, lies in the local different. -/
theorem FF.span_nat_mul_point_conductor_le_different (M : FF ℤ_[3] ℚ_[3])
    (n : ℕ) (hn : KilledBy n M)
    (f : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers L) :
    Ideal.span {(n : ThreeAdicIntegers L)} * f.range.conductorIdeal ≤
      differentIdeal ℤ_[3] (ThreeAdicIntegers L) := by
  rw [threeAdicDifferent_eq_annihilator_kaehlerDifferential]
  exact M.span_nat_mul_point_conductor_le_annihilator n hn f

/-- A conductor element of a killed-by-three integral point yields an
explicit element of the local different. -/
theorem FF.three_mul_mem_different_of_point_conductor (M : FF ℤ_[3] ℚ_[3])
    (hM : KilledBy 3 M) (f : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers L)
    {c : ThreeAdicIntegers L} (hc : c ∈ f.range.conductorIdeal) :
    3 * c ∈ differentIdeal ℤ_[3] (ThreeAdicIntegers L) :=
  M.span_nat_mul_point_conductor_le_different L 3 hM f
    (Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton _)) hc)

/-- A nonzero conductor bounds the loss in transferring the differential
annihilator from a killed-by-three model to a local ring of integers. -/
theorem FF.normalizedDifferentExponent_le_one_add_conductor (M : FF ℤ_[3] ℚ_[3])
    (hM : KilledBy 3 M) (f : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers L)
    (hf : f.range.conductorIdeal ≠ ⊥) :
    normalizedDifferentExponent L ≤ 1 + normalizedIdealOrder L f.range.conductorIdeal := by
  have : CharZero (ThreeAdicIntegers L) := Algebra.charZero_of_charZero ℤ_[3] _
  have h3 : Ideal.span {(3 : ThreeAdicIntegers L)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num
  have h := normalizedIdealOrder_antitone L (mul_ne_zero h3 hf)
    (M.span_nat_mul_point_conductor_le_different L 3 hM f)
  simpa only [normalizedIdealOrder_mul L h3 hf, normalizedIdealOrder_three,
    normalizedDifferentExponent] using h

/-- A nonzero conductor element bounds the different without choosing a
generator for the conductor ideal. -/
theorem FF.normalizedDifferentExponent_le_one_add_order_of_point_conductor
    (M : FF ℤ_[3] ℚ_[3]) (hM : KilledBy 3 M)
    (f : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers L)
    {c : ThreeAdicIntegers L} (hc : c ∈ f.range.conductorIdeal) (hc0 : c ≠ 0) :
    normalizedDifferentExponent L ≤ 1 + normalizedIdealOrder L (Ideal.span {c}) := by
  have hspan : Ideal.span {c} ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hc0
  have hle : Ideal.span {c} ≤ f.range.conductorIdeal := Ideal.span_le.mpr (by simpa using hc)
  exact (M.normalizedDifferentExponent_le_one_add_conductor L hM f
    (ne_bot_of_le_ne_bot hspan hle)).trans
      (add_le_add (le_refl 1) (normalizedIdealOrder_antitone L hspan hle))

/-- A conductor correction of order strictly below one half suffices for
the strict Fontaine numerical bound. The small-conductor premise is explicit. -/
theorem FF.normalizedDifferentExponent_lt_three_halves_of_point_conductor
    (M : FF ℤ_[3] ℚ_[3]) (hM : KilledBy 3 M)
    (f : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers L)
    {c : ThreeAdicIntegers L} (hc : c ∈ f.range.conductorIdeal) (hc0 : c ≠ 0)
    (hsmall : normalizedIdealOrder L (Ideal.span {c}) < (1 / 2 : ℚ)) :
    normalizedDifferentExponent L < (3 / 2 : ℚ) := by
  have h := M.normalizedDifferentExponent_le_one_add_order_of_point_conductor L hM f hc hc0
  linarith

/-- If the integral point already generates the full ring of integers,
there is no conductor loss and the different exponent is at most one. -/
theorem FF.normalizedDifferentExponent_le_one_of_surjective_point
    (M : FF ℤ_[3] ℚ_[3]) (hM : KilledBy 3 M)
    (f : M.CoordinateRing →ₐ[ℤ_[3]] ThreeAdicIntegers L) (hf : Function.Surjective f) :
    normalizedDifferentExponent L ≤ 1 := by
  apply normalizedDifferentExponent_le_of_kaehler_annihilation L
    (threeAdicIntegersPowerBasis L) 1
  intro ω
  calc
    (3 : ℤ_[3]) ^ 1 • ω = (3 : ℕ) • ω := by
      rw [pow_one]
      exact Nat.cast_smul_eq_nsmul ℤ_[3] 3 ω
    _ = 0 := M.nsmul_differential_eq_zero_of_surjective_point 3 hM f hf ω

end ThreeAdicPlan
