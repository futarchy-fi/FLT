/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineProperty
public import FLT.GroupScheme.LocalIntegralPowerBasis

/-!
# Spectral norms and normalized ideal orders

Comparison of the spectral-norm cutoff defining Fontaine's property with
the ideal-factorization normalization defining the different exponent.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (L : Type*) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]

/-- The maximal ideal has ideal order one. -/
@[simp] theorem threeAdicIdealOrder_maximalIdeal :
    threeAdicIdealOrder L (IsLocalRing.maximalIdeal (ThreeAdicIntegers L)) = 1 := by
  classical
  have hp : Irreducible (IsLocalRing.maximalIdeal (ThreeAdicIntegers L)) :=
    ((Ideal.prime_iff_isPrime (IsDiscreteValuationRing.not_a_field _)).mpr
      inferInstance).irreducible
  simp [threeAdicIdealOrder, UniqueFactorizationMonoid.normalizedFactors_irreducible hp]

/-- Every nonzero ideal is the corresponding power of the maximal ideal,
with exponent given by `threeAdicIdealOrder`. -/
theorem ideal_eq_maximalIdeal_pow_threeAdicIdealOrder
    (I : Ideal (ThreeAdicIntegers L)) (hI : I ≠ ⊥) :
    I = IsLocalRing.maximalIdeal (ThreeAdicIntegers L) ^ threeAdicIdealOrder L I := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (ThreeAdicIntegers L)
  obtain ⟨n, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hπ
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq,
    threeAdicIdealOrder_pow, threeAdicIdealOrder_maximalIdeal, mul_one]

/-- An integral unit has spectral norm one. -/
theorem spectralNorm_unit (u : (ThreeAdicIntegers L)ˣ) :
    spectralNorm ℚ_[3] L ((u : ThreeAdicIntegers L) : L) = 1 := by
  let := spectralNorm.nontriviallyNormedField ℚ_[3] L
  have hu := (isIntegral_iff_spectralNorm_le_one L ((u : ThreeAdicIntegers L) : L)).mp
    (u : ThreeAdicIntegers L).property
  have hv := (isIntegral_iff_spectralNorm_le_one L ((↑u⁻¹ : ThreeAdicIntegers L) : L)).mp
    (↑u⁻¹ : ThreeAdicIntegers L).property
  change ‖((u : ThreeAdicIntegers L) : L)‖ = 1
  apply le_antisymm hu
  have hmul : ((u : ThreeAdicIntegers L) : L) * ((↑u⁻¹ : ThreeAdicIntegers L) : L) = 1 := by
    exact_mod_cast u.mul_inv
  have h := norm_mul ((u : ThreeAdicIntegers L) : L) ((↑u⁻¹ : ThreeAdicIntegers L) : L)
  rw [hmul, norm_one] at h
  calc
    1 = ‖((u : ThreeAdicIntegers L) : L)‖ *
        ‖((↑u⁻¹ : ThreeAdicIntegers L) : L)‖ := h
    _ ≤ ‖((u : ThreeAdicIntegers L) : L)‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ = _ := mul_one _

/-- Equal principal integral ideals have generators of the same spectral norm. -/
theorem spectralNorm_eq_of_span_eq {x y : ThreeAdicIntegers L}
    (h : Ideal.span {x} = Ideal.span {y}) :
    spectralNorm ℚ_[3] L (x : L) = spectralNorm ℚ_[3] L (y : L) := by
  let := spectralNorm.nontriviallyNormedField ℚ_[3] L
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp h : Associated x y)
  have heq : (x : L) * ((u : ThreeAdicIntegers L) : L) = (y : L) := by exact_mod_cast hu
  change ‖(x : L)‖ = ‖(y : L)‖
  rw [← heq, norm_mul]
  change _ = _ * spectralNorm ℚ_[3] L ((u : ThreeAdicIntegers L) : L)
  rw [spectralNorm_unit, mul_one]

/-- The spectral norm of a nonzero integral element is determined by the
normalized order of its principal ideal. -/
theorem spectralNorm_eq_rpow_normalizedIdealOrder (x : ThreeAdicIntegers L) (hx : x ≠ 0) :
    spectralNorm ℚ_[3] L (x : L) =
      (3 : ℝ) ^ (-(normalizedIdealOrder L (Ideal.span {x}) : ℝ)) := by
  let := spectralNorm.nontriviallyNormedField ℚ_[3] L
  have : CharZero (ThreeAdicIntegers L) := Algebra.charZero_of_charZero ℤ_[3] _
  let n := threeAdicIdealOrder L (Ideal.span {x})
  let e := threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)})
  have he : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.ne_of_gt (threeAdicIdealOrder_three_pos L))
  have hIx : Ideal.span {x} ≠ ⊥ := by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hx
  have hI3 : Ideal.span {(3 : ThreeAdicIntegers L)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num
  have hspan : Ideal.span {x ^ e} = Ideal.span {(3 : ThreeAdicIntegers L) ^ n} := by
    rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow,
      ideal_eq_maximalIdeal_pow_threeAdicIdealOrder L _ hIx,
      ideal_eq_maximalIdeal_pow_threeAdicIdealOrder L _ hI3, ← pow_mul, ← pow_mul]
    exact congrArg _ (Nat.mul_comm n e)
  have hpow := spectralNorm_eq_of_span_eq L hspan
  change ‖(x : L) ^ e‖ = spectralNorm ℚ_[3] L ((3 : L) ^ n) at hpow
  rw [norm_pow] at hpow
  have h3 := spectralNorm_extends (K := ℚ_[3]) (L := L) ((3 : ℚ_[3]) ^ n)
  simp only [map_pow, map_ofNat] at h3
  rw [h3] at hpow
  have hp := Padic.norm_p_pow (p := 3) n
  norm_num only [Nat.cast_ofNat] at hp
  rw [hp, ← Real.rpow_intCast] at hpow
  simp only [Int.cast_neg, Int.cast_natCast] at hpow
  change ‖(x : L)‖ = _
  calc
    ‖(x : L)‖ = (‖(x : L)‖ ^ (e : ℝ)) ^ (1 / (e : ℝ)) := by
      rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel he, Real.rpow_one]
    _ = ((3 : ℝ) ^ (-(n : ℝ))) ^ (1 / (e : ℝ)) := by
      rw [Real.rpow_natCast, hpow]
    _ = (3 : ℝ) ^ (-((n : ℝ) / (e : ℝ))) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    _ = _ := by simp [normalizedIdealOrder, n, e]

/-- For nonzero elements, the spectral cutoff is precisely the normalized
principal-ideal order inequality. -/
theorem mem_threeAdicValuationIdeal_iff_order (x : ThreeAdicIntegers L) (hx : x ≠ 0) (m : ℚ) :
    x ∈ threeAdicValuationIdeal L m ↔ m ≤ normalizedIdealOrder L (Ideal.span {x}) := by
  rw [mem_threeAdicValuationIdeal, spectralNorm_eq_rpow_normalizedIdealOrder L x hx,
    Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3), neg_le_neg_iff, Rat.cast_le]

/-- Containment of a nonzero ideal in the valuation cutoff is equivalent to
the corresponding lower bound on its normalized ideal order. -/
theorem le_threeAdicValuationIdeal_iff (I : Ideal (ThreeAdicIntegers L)) (hI : I ≠ ⊥) (m : ℚ) :
    I ≤ threeAdicValuationIdeal L m ↔ m ≤ normalizedIdealOrder L I := by
  obtain ⟨x, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
  have hx : x ≠ 0 := by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hI
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact mem_threeAdicValuationIdeal_iff_order L x hx m

/-- The desired strict different bound is equivalent to failure of containment
of the different in the valuation cutoff. -/
theorem normalizedDifferentExponent_lt_iff_not_le_valuationIdeal (m : ℚ) :
    normalizedDifferentExponent L < m ↔
      ¬ differentIdeal ℤ_[3] (ThreeAdicIntegers L) ≤ threeAdicValuationIdeal L m := by
  rw [le_threeAdicValuationIdeal_iff L _ (threeAdicDifferent_ne_bot L), not_le]
  rfl

/-- In the canonical integral power basis, the strict different bound is
exactly a lower bound on the norm of the minimal-polynomial derivative. -/
theorem normalizedDifferentExponent_lt_iff_derivative_norm (m : ℚ) :
    normalizedDifferentExponent L < m ↔
      (3 : ℝ) ^ (-(m : ℝ)) < spectralNorm ℚ_[3] L
        ((Polynomial.aeval (threeAdicIntegersPowerBasis L).gen
          (Polynomial.derivative (minpoly ℤ_[3] (threeAdicIntegersPowerBasis L).gen)) :
            ThreeAdicIntegers L) : L) := by
  rw [normalizedDifferentExponent_lt_iff_not_le_valuationIdeal,
    (threeAdicIntegersPowerBasis L).differentIdeal_eq_span_minpoly_derivative ℚ_[3] L,
    Ideal.span_le, Set.singleton_subset_iff]
  change (¬ spectralNorm ℚ_[3] L _ ≤ (3 : ℝ) ^ (-(m : ℝ))) ↔ _
  exact not_le

end ThreeAdicPlan
