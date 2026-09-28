/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalDifferentInertia
public import FLT.Mathlib.RingTheory.Valuation.PolynomialObstruction

/-!
# Forbidden values of an integral minimal polynomial

The discrete valuation on the full ring of integers agrees with the ideal
orders used for the different. A minimal polynomial of an integral power
basis cannot take a nonzero value whose order is one step below the sum of
the different order and the largest conjugate displacement.
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

/-- An isomorphism of discrete valuation rings preserves their additive valuations. -/
theorem addValRingEquiv (e : R ≃+* S) (x : R) : addVal S (e x) = addVal R x := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hπ
  rw [addVal_def' u hπ n]
  apply addVal_def _ (Units.map e.toMonoidHom u) (hπ.map e) n
  simp

end IsDiscreteValuationRing

namespace ThreeAdicPlan

variable (L : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]

/-- For a nonzero integer, the additive DVR valuation equals its principal-ideal order. -/
theorem threeAdicAddValEqIdealOrder (x : ThreeAdicIntegers L) (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal (ThreeAdicIntegers L) x =
      (threeAdicIdealOrder L (Ideal.span {x}) : ℕ∞) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (ThreeAdicIntegers L)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  rw [IsDiscreteValuationRing.addVal_def' u hπ n,
    Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hπ.maximalIdeal_eq, threeAdicIdealOrder_pow, threeAdicIdealOrder_maximalIdeal, mul_one]

/-- Integral automorphisms preserve the additive valuation. -/
theorem threeAdicAddValAut (σ : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L)
    (x : ThreeAdicIntegers L) :
    IsDiscreteValuationRing.addVal (ThreeAdicIntegers L) (σ x) =
      IsDiscreteValuationRing.addVal (ThreeAdicIntegers L) x :=
  IsDiscreteValuationRing.addValRingEquiv σ.toRingEquiv x

/-- The generator displacement of a nonidentity automorphism has the order
of its displacement ideal. -/
theorem threeAdicAddValGenSubAut
    (σ : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L) (hσ : σ ≠ 1) :
    IsDiscreteValuationRing.addVal (ThreeAdicIntegers L)
      ((threeAdicIntegersPowerBasis L).gen - σ (threeAdicIntegersPowerBasis L).gen) =
        (threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.toAlgHom) : ℕ∞) := by
  have hhom : σ.toAlgHom ≠ AlgHom.id ℤ_[3] (ThreeAdicIntegers L) := by
    intro h
    apply hσ
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun f : ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers L ↦ f x) h
  rw [threeAdicDisplacementIdealEqSpan L (threeAdicIntegersPowerBasis L)]
  apply threeAdicAddValEqIdealOrder
  intro h
  apply hhom
  exact (threeAdicIntegersPowerBasis L).algHom_ext (sub_eq_zero.mp h).symm

/-- The integral minimal polynomial factors over the integral automorphisms. -/
theorem threeAdicIntegralMinpolyEqProdAut [IsGalois ℚ_[3] L] :
    (minpoly ℤ_[3] (threeAdicIntegersPowerBasis L).gen).map
      (algebraMap ℤ_[3] (ThreeAdicIntegers L)) =
        ∏ σ : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L,
          (Polynomial.X - Polynomial.C (σ (threeAdicIntegersPowerBasis L).gen)) := by
  rw [(threeAdicIntegersPowerBasis L).minpolyEqProdHom
    (threeAdicIntegralMinpolySplits L _) (threeAdicIntegralMinpolyRootsNodup L _)]
  symm
  apply Fintype.prod_equiv (threeAdicIntegralAutEquivHom L)
  intro σ
  rw [threeAdicIntegralAutEquivHomApply]
  rfl

open scoped Classical in
/-- The unnormalized different order is the sum of the nonidentity
integral automorphisms' displacement orders. -/
theorem threeAdicDifferentOrderEqSumAut [IsGalois ℚ_[3] L] :
    threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L)) =
      ∑ σ ∈ Finset.univ.erase (1 : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L),
        threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.toAlgHom) := by
  classical
  let G := ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L
  have h := normalizedDifferentExponentEqSumDisplacement L
  rw [← Fintype.sum_equiv (threeAdicIntegralAutEquivHom L)
    (fun σ : G ↦ threeAdicDisplacementOrder L σ.toAlgHom)
    (threeAdicDisplacementOrder L) (fun σ ↦ by rw [threeAdicIntegralAutEquivHomApply])] at h
  have he : (threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (threeAdicIdealOrder_three_pos L))
  simp only [normalizedDifferentExponent, threeAdicDisplacementOrder,
    normalizedIdealOrder, ← Finset.sum_div] at h
  have hsum : threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L)) =
      ∑ σ : G, threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.toAlgHom) := by
    exact_mod_cast (div_left_inj' he).mp h
  rw [hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : G))]
  suffices hz : threeAdicIdealOrder L (threeAdicDisplacementIdeal L (1 : G).toAlgHom) = 0 by
    rw [hz, add_zero]
  have hid : threeAdicDisplacementIdeal L (1 : G).toAlgHom = 0 := by
    change Ideal.span (Set.range fun x : ThreeAdicIntegers L ↦ x - x) = 0
    simp only [sub_self, Set.range_const, Ideal.span_singleton_zero]
    rfl
  rw [hid]
  simp only [threeAdicIdealOrder, UniqueFactorizationMonoid.normalizedFactors_zero,
    Multiset.count_zero]

/-- A largest positive conjugate displacement excludes the critical value
of the integral minimal polynomial throughout the original field. -/
theorem threeAdicMinpolyAddValNeCritical [IsGalois ℚ_[3] L] (c : ℕ)
    (hbound : ∀ σ : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L, σ ≠ 1 →
      threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.toAlgHom) ≤ c)
    (hmax : ∃ σ : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L, σ ≠ 1 ∧
      threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.toAlgHom) = c)
    (hc : 0 < c) (x : ThreeAdicIntegers L) :
    IsDiscreteValuationRing.addVal (ThreeAdicIntegers L)
      (Polynomial.aeval x (minpoly ℤ_[3] (threeAdicIntegersPowerBasis L).gen)) ≠
        ((threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L)) + c - 1 : ℕ) :
          ℕ∞) := by
  classical
  rw [← Polynomial.eval_map_algebraMap, threeAdicIntegralMinpolyEqProdAut,
    Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  apply AddValuation.orbitProdSubNeCritical
    (IsDiscreteValuationRing.addVal (ThreeAdicIntegers L))
    (fun σ x ↦ threeAdicAddValAut L σ x) (threeAdicIntegersPowerBasis L).gen
    (fun σ ↦ threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.toAlgHom))
    _ c (fun σ hσ ↦ threeAdicAddValGenSubAut L σ hσ)
    (threeAdicDifferentOrderEqSumAut L).symm hbound hmax hc

end ThreeAdicPlan
