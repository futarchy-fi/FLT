/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalDifferentValuation
public import FLT.GroupScheme.LocalIntegralPowerBasis

/-!
# Transporting the normalized local different

An isomorphism of finite three-adic extensions identifies their rings of
integers, different ideals, ideal orders, and normalized different exponents.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable {L E : Type*} [Field L] [Field E]
  [Algebra ℚ_[3] L] [Algebra ℤ_[3] L] [IsScalarTower ℤ_[3] ℚ_[3] L]
  [FiniteDimensional ℚ_[3] L]
  [Algebra ℚ_[3] E] [Algebra ℤ_[3] E] [IsScalarTower ℤ_[3] ℚ_[3] E]
  [FiniteDimensional ℚ_[3] E]

/-- A three-adic field isomorphism restricts to an isomorphism of the full integer rings. -/
def threeAdicIntegersEquiv (e : L ≃ₐ[ℚ_[3]] E) :
    ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers E :=
  (e.restrictScalars ℤ_[3]).mapIntegralClosure

/-- The trace-dual different transports along an isomorphism of the integer rings. -/
theorem map_threeAdicDifferent
    (e : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers E) :
    (differentIdeal ℤ_[3] (ThreeAdicIntegers L)).map e.toRingHom =
      differentIdeal ℤ_[3] (ThreeAdicIntegers E) := by
  let pb := threeAdicIntegersPowerBasis L
  rw [pb.differentIdeal_eq_span_minpoly_derivative ℚ_[3] L,
    (pb.map e).differentIdeal_eq_span_minpoly_derivative ℚ_[3] E,
    Ideal.map_span, Set.image_singleton, PowerBasis.map_gen, minpoly.algEquiv_eq]
  congr 2
  exact (Polynomial.aeval_algHom_apply e _ _).symm

/-- Isomorphisms of the full integer rings preserve maximal-ideal order. -/
theorem threeAdicIdealOrder_map
    (e : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers E)
    (I : Ideal (ThreeAdicIntegers L)) :
    threeAdicIdealOrder E (I.map e.toRingHom) = threeAdicIdealOrder L I := by
  by_cases hI : I = ⊥
  · subst I
    rw [Ideal.map_bot]
    change (UniqueFactorizationMonoid.normalizedFactors
        (0 : Ideal (ThreeAdicIntegers E))).count _ =
      (UniqueFactorizationMonoid.normalizedFactors (0 : Ideal (ThreeAdicIntegers L))).count _
    simp only [UniqueFactorizationMonoid.normalizedFactors_zero, Multiset.count_zero]
  have hmap : I.map e.toRingHom =
      IsLocalRing.maximalIdeal (ThreeAdicIntegers E) ^ threeAdicIdealOrder L I := by
    conv_lhs => rw [ideal_eq_maximalIdeal_pow_threeAdicIdealOrder L I hI]
    rw [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective]
  rw [hmap, threeAdicIdealOrder_pow, threeAdicIdealOrder_maximalIdeal, mul_one]

/-- The denominator used to normalize at three is invariant under integer-ring isomorphism. -/
theorem threeAdicIdealOrder_three_eq
    (e : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers E) :
    threeAdicIdealOrder E (Ideal.span {(3 : ThreeAdicIntegers E)}) =
      threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) := by
  simpa only [Ideal.map_span, Set.image_singleton, map_ofNat] using
    threeAdicIdealOrder_map e (Ideal.span {(3 : ThreeAdicIntegers L)})

/-- The normalized different exponent is an invariant of the three-adic extension. -/
theorem normalizedDifferentExponent_eq_of_algEquiv (e : L ≃ₐ[ℚ_[3]] E) :
    normalizedDifferentExponent L = normalizedDifferentExponent E := by
  let eO := threeAdicIntegersEquiv e
  unfold normalizedDifferentExponent normalizedIdealOrder
  rw [← map_threeAdicDifferent eO, threeAdicIdealOrder_map,
    threeAdicIdealOrder_three_eq eO]

end ThreeAdicPlan
