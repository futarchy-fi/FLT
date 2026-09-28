/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineDifferentReduction
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Inertia and large displacements

The cardinality of integral inertia is the denominator used to normalize
ideal orders. This compares the displacement sum for the different with
the `1/e` correction in Fontaine's obstruction theorem.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (L : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]

/-- Every integral endomorphism of a finite local extension is an automorphism. -/
def threeAdicIntegralAutEquivHom :
    (ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L) ≃
      (ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers L) :=
  (galRestrict ℤ_[3] ℚ_[3] L (ThreeAdicIntegers L)).toEquiv.symm.trans
    ((Algebra.IsAlgebraic.algEquivEquivAlgHom ℚ_[3] L).toEquiv.trans
      (galRestrictHom ℤ_[3] ℚ_[3] L (ThreeAdicIntegers L)).toEquiv)

/-- The automorphism-to-endomorphism equivalence forgets the inverse. -/
@[simp] theorem threeAdicIntegralAutEquivHomApply
    (σ : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L) :
    threeAdicIntegralAutEquivHom L σ = σ.toAlgHom := by
  change galRestrictHom ℤ_[3] ℚ_[3] L (ThreeAdicIntegers L)
    (((galRestrict ℤ_[3] ℚ_[3] L (ThreeAdicIntegers L)).symm σ).toAlgHom) = _
  rw [← coe_galRestrict_apply, MulEquiv.apply_symm_apply]

/-- Integral automorphisms form a finite group. -/
instance threeAdicIntegralAutFintype :
    Fintype (ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L) :=
  Fintype.ofEquiv _ (threeAdicIntegralAutEquivHom L).symm

/-- In a normal extension, the integral automorphisms have fixed ring `ℤ_[3]`. -/
instance threeAdicIntegralAutGaloisGroup [IsGalois ℚ_[3] L] :
    IsGaloisGroup (ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L)
      ℤ_[3] (ThreeAdicIntegers L) where
  faithful := inferInstance
  commutes := inferInstance
  isInvariant := Algebra.isInvariant_of_isGalois' ℤ_[3] ℚ_[3] L (ThreeAdicIntegers L)

/-- The ideal-order denominator is the usual ramification index. -/
theorem threeAdicIdealOrderThreeEqRamificationIdx :
    threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) =
      (IsLocalRing.maximalIdeal (ThreeAdicIntegers L)).ramificationIdx ℤ_[3] := by
  let instCharZero : CharZero (ThreeAdicIntegers L) :=
    Algebra.charZero_of_charZero ℤ_[3] _
  have hmap : (IsLocalRing.maximalIdeal ℤ_[3]).map
      (algebraMap ℤ_[3] (ThreeAdicIntegers L)) = Ideal.span {(3 : ThreeAdicIntegers L)} := by
    simp only [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
      Nat.cast_ofNat, map_ofNat]
  have hmapne : (IsLocalRing.maximalIdeal ℤ_[3]).map
      (algebraMap ℤ_[3] (ThreeAdicIntegers L)) ≠ ⊥ := by
    rw [hmap, ne_eq, Ideal.span_singleton_eq_bot]
    norm_num
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    (IsLocalRing.maximalIdeal ℤ_[3]) _ hmapne, hmap]
  rfl

/-- The inertia group of the full ring of integers has cardinality equal
to the ideal-order denominator. -/
theorem threeAdicInertiaCard [IsGalois ℚ_[3] L] :
    Nat.card ((IsLocalRing.maximalIdeal (ThreeAdicIntegers L)).inertia
      (ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L)) =
      threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) := by
  let p := IsLocalRing.maximalIdeal ℤ_[3]
  let P := IsLocalRing.maximalIdeal (ThreeAdicIntegers L)
  let instFiniteQuotient : Finite (ℤ_[3] ⧸ p) :=
    Finite.of_equiv (ZMod 3) PadicInt.residueField.symm.toEquiv
  let instFiniteResidue : Finite p.ResidueField := inferInstance
  rw [Ideal.card_inertia_eq_ramificationIdxIn p P,
    Ideal.ramificationIdxIn_eq_ramificationIdx p P
      (ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L),
    ← threeAdicIdealOrderThreeEqRamificationIdx]

/-- An automorphism outside inertia has displacement order zero. -/
theorem threeAdicDisplacementOrderEqZeroOfNotInertia
    (σ : ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L)
    (hσ : σ ∉ (IsLocalRing.maximalIdeal (ThreeAdicIntegers L)).inertia
      (ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L)) :
    threeAdicDisplacementOrder L σ.toAlgHom = 0 := by
  have htop : threeAdicDisplacementIdeal L σ.toAlgHom = ⊤ := by
    by_contra h
    apply hσ
    rw [Ideal.mem_inertia]
    intro x
    have hx := IsLocalRing.le_maximalIdeal h
      (Ideal.subset_span (show x - σ x ∈ Set.range (fun y ↦ y - σ.toAlgHom y) from ⟨x, rfl⟩))
    change σ x - x ∈ IsLocalRing.maximalIdeal (ThreeAdicIntegers L)
    exact (neg_sub x (σ x)) ▸ (IsLocalRing.maximalIdeal (ThreeAdicIntegers L)).neg_mem hx
  rw [threeAdicDisplacementOrder, htop]
  rw [← Ideal.one_eq_top]
  simp only [normalizedIdealOrder, threeAdicIdealOrder,
    UniqueFactorizationMonoid.normalizedFactors_one, Multiset.count_zero, Nat.cast_zero, zero_div]

/-- If every displacement is at most one valuation step, the different
exponent is strictly less than one. Only inertia contributes to the sum. -/
theorem normalizedDifferentExponentLtOneOfDisplacementLe [IsGalois ℚ_[3] L]
    (hsmall : ∀ σ : ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers L,
      threeAdicDisplacementOrder L σ ≤
        1 / (threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) : ℚ)) :
    normalizedDifferentExponent L < 1 := by
  classical
  let G := ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L
  let H := (IsLocalRing.maximalIdeal (ThreeAdicIntegers L)).inertia G
  let e := threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)})
  have he : (0 : ℚ) < e := Nat.cast_pos.mpr (threeAdicIdealOrder_three_pos L)
  have hsum : normalizedDifferentExponent L =
      ∑ σ : G, threeAdicDisplacementOrder L σ.toAlgHom := by
    rw [normalizedDifferentExponentEqSumDisplacement]
    exact (Fintype.sum_equiv (threeAdicIntegralAutEquivHom L)
      (fun σ ↦ threeAdicDisplacementOrder L σ.toAlgHom)
      (threeAdicDisplacementOrder L) (fun σ ↦ by rw [threeAdicIntegralAutEquivHomApply])).symm
  calc
    normalizedDifferentExponent L = ∑ σ : G, threeAdicDisplacementOrder L σ.toAlgHom := hsum
    _ < ∑ σ : G, if σ ∈ H then (1 / (e : ℚ)) else 0 := by
      apply Finset.sum_lt_sum
      · intro σ _
        split_ifs with hσ
        · exact hsmall σ.toAlgHom
        · exact le_of_eq (threeAdicDisplacementOrderEqZeroOfNotInertia L σ hσ)
      · refine ⟨1, Finset.mem_univ _, ?_⟩
        simp only [Subgroup.one_mem, ite_true]
        change threeAdicDisplacementOrder L (AlgHom.id ℤ_[3] (ThreeAdicIntegers L)) < _
        rw [threeAdicDisplacementOrderId]
        exact one_div_pos.mpr he
    _ = (Fintype.card H : ℚ) / e := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      rw [Fintype.card_subtype]
    _ = 1 := by
      rw [← Nat.card_eq_fintype_card, threeAdicInertiaCard]
      exact div_self (ne_of_gt he)

/-- Once the different exponent reaches one, some displacement exceeds the
`1/e` correction appearing in Fontaine's Proposition 1.5(ii). -/
theorem existsDisplacementGtReciprocalRamificationOfDifferentGeOne [IsGalois ℚ_[3] L]
    (hd : 1 ≤ normalizedDifferentExponent L) :
    ∃ σ : ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers L,
      σ ≠ AlgHom.id ℤ_[3] (ThreeAdicIntegers L) ∧
      1 / (threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) : ℚ) <
        threeAdicDisplacementOrder L σ := by
  classical
  have hpos : ∃ σ : ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers L,
      1 / (threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) : ℚ) <
        threeAdicDisplacementOrder L σ := by
    by_contra h
    push Not at h
    exact (not_lt_of_ge hd) (normalizedDifferentExponentLtOneOfDisplacementLe L h)
  obtain ⟨σ, hσ⟩ := hpos
  refine ⟨σ, ?_, hσ⟩
  rintro rfl
  rw [threeAdicDisplacementOrderId] at hσ
  have he : (0 : ℚ) < threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) :=
    Nat.cast_pos.mpr (threeAdicIdealOrder_three_pos L)
  exact (not_lt_of_ge (le_of_lt (one_div_pos.mpr he))) hσ

/-- At any cutoff at least one, Fontaine's corrected obstruction suffices
for a strict different bound. Only the arithmetic obstruction remains a premise. -/
theorem normalizedDifferentExponentLtOfCorrectedFontaineObstructions [IsGalois ℚ_[3] L]
    (u : ℚ) (hu : 1 ≤ u)
    (hP : ∀ m : ℚ, u < m → FontaineProperty (ThreeAdicIntegers L) m)
    (hbad : ∀ σ : ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers L,
      σ ≠ AlgHom.id ℤ_[3] (ThreeAdicIntegers L) → ∀ m : ℚ, 0 < m →
      m < normalizedDifferentExponent L + threeAdicDisplacementOrder L σ -
        1 / (threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) : ℚ) →
      ¬ FontaineProperty (ThreeAdicIntegers L) m) :
    normalizedDifferentExponent L < u := by
  apply normalizedDifferentExponentLtOfFontaineObstructions L u _ (by linarith) hP
  · intro hud
    exact existsDisplacementGtReciprocalRamificationOfDifferentGeOne L (hu.trans hud)
  · exact hbad

/-- Fontaine's original `1/e` correction suffices at the cutoff `3/2`.
The counterexample construction is still an explicit hypothesis. -/
theorem normalizedDifferentExponentLtThreeHalvesOfCorrectedFontaineObstructions
    [IsGalois ℚ_[3] L]
    (hP : ∀ m : ℚ, (3 / 2 : ℚ) < m → FontaineProperty (ThreeAdicIntegers L) m)
    (hbad : ∀ σ : ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers L,
      σ ≠ AlgHom.id ℤ_[3] (ThreeAdicIntegers L) → ∀ m : ℚ, 0 < m →
      m < normalizedDifferentExponent L + threeAdicDisplacementOrder L σ -
        1 / (threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) : ℚ) →
      ¬ FontaineProperty (ThreeAdicIntegers L) m) :
    normalizedDifferentExponent L < (3 / 2 : ℚ) :=
  normalizedDifferentExponentLtOfCorrectedFontaineObstructions L (3 / 2) (by norm_num) hP hbad

end ThreeAdicPlan
