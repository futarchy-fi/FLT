/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalInertiaPolynomial

/-!
# Choosing the largest inertia displacement

A positive corrected Fontaine cutoff is bounded by the critical exponent
of a largest nonidentity inertia displacement. Displacements outside inertia
vanish and therefore do not affect this maximum.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (L : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L] [IsGalois ℚ_[3] L]

/-- A positive corrected cutoff admits a positive maximal inertia displacement
whose critical exponent bounds the requested precision. -/
theorem existsThreeAdicInertiaCriticalData
    (σ : ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers L)
    (hσ : σ ≠ AlgHom.id ℤ_[3] (ThreeAdicIntegers L)) (m : ℚ) (hm : 0 < m)
    (hcut : m < normalizedDifferentExponent L + threeAdicDisplacementOrder L σ -
      1 / (threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) : ℚ)) :
    ∃ c : ℕ, 0 < c ∧
      (∀ τ : ThreeAdicIntegralInertia L, τ ≠ 1 →
        threeAdicIdealOrder L (threeAdicDisplacementIdeal L τ.val.toAlgHom) ≤ c) ∧
      (∃ τ : ThreeAdicIntegralInertia L, τ ≠ 1 ∧
        threeAdicIdealOrder L (threeAdicDisplacementIdeal L τ.val.toAlgHom) = c) ∧
      m ≤
        ((threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L)) + c - 1 : ℕ) : ℚ) /
          threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) := by
  classical
  let G := ThreeAdicIntegers L ≃ₐ[ℤ_[3]] ThreeAdicIntegers L
  let k := fun τ : G => threeAdicIdealOrder L (threeAdicDisplacementIdeal L τ.toAlgHom)
  let τ := (threeAdicIntegralAutEquivHom L).symm σ
  have hτ : τ.toAlgHom = σ := by
    rw [← threeAdicIntegralAutEquivHomApply]
    exact (threeAdicIntegralAutEquivHom L).apply_symm_apply σ
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hσ
    rw [← hτ, h]
    rfl
  obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image (Finset.univ.erase (1 : G)) k
    ⟨τ, Finset.mem_erase.mpr ⟨hτ1, Finset.mem_univ _⟩⟩
  have hbound : ∀ ν : G, ν ≠ 1 → k ν ≤ k μ :=
    fun ν hν => hmax ν (Finset.mem_erase.mpr ⟨hν, Finset.mem_univ _⟩)
  let D := threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L))
  let e := threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)})
  have he : (0 : ℚ) < e := Nat.cast_pos.mpr (threeAdicIdealOrder_three_pos L)
  have hcut' : m < (D : ℚ) / e + (k τ : ℚ) / e - 1 / e := by
    simpa only [normalizedDifferentExponent, threeAdicDisplacementOrder,
      normalizedIdealOrder, ← hτ] using hcut
  have hc : 0 < k μ := by
    by_contra h
    have hz : k μ = 0 := Nat.eq_zero_of_not_pos h
    have hD : D = 0 := by
      change threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L)) = 0
      rw [threeAdicDifferentOrderEqSumAut]
      apply Finset.sum_eq_zero
      intro ν hν
      exact Nat.eq_zero_of_le_zero (hz ▸ hbound ν (Finset.mem_erase.mp hν).1)
    have hτz : k τ = 0 := Nat.eq_zero_of_le_zero (hz ▸ hbound τ hτ1)
    rw [hD, hτz, Nat.cast_zero, zero_div, zero_add, zero_sub] at hcut'
    have hp := one_div_pos.mpr he
    linarith
  have hμH : μ ∈ ThreeAdicIntegralInertia L := by
    by_contra h
    have hz := threeAdicDisplacementIdealOrderZeroOutsideInertia L μ h
    exact (Nat.ne_of_gt hc) hz
  refine ⟨k μ, hc, ?_, ?_, ?_⟩
  · intro ν hν
    apply hbound
    intro h
    exact hν (Subtype.ext h)
  · exact ⟨⟨μ, hμH⟩, fun h => (Finset.mem_erase.mp hμ).1
      (congrArg Subtype.val h), rfl⟩
  · have hk : (k τ : ℚ) ≤ k μ := Nat.cast_le.mpr (hbound τ hτ1)
    have hN : ((D + k μ - 1 : ℕ) : ℚ) = (D : ℚ) + k μ - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    change m ≤ ((D + k μ - 1 : ℕ) : ℚ) / e
    rw [hN]
    apply (le_div_iff₀ he).mpr
    have hh : m * e < (D : ℚ) + k τ - 1 := (lt_div_iff₀ he).mp (by
      convert hcut' using 1; ring)
    linarith

/-- Nontrivial inertia forces ramification index greater than one. -/
theorem threeAdicRamificationGtOneOfNontrivialInertia
    (σ : ThreeAdicIntegralInertia L) (hσ : σ ≠ 1) :
    1 < threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) := by
  classical
  rw [← threeAdicInertiaCard L, Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card_iff.mpr ⟨σ, 1, hσ⟩

/-- If all inertia displacements are at most one, the different order is
at most the ramification index minus one. -/
theorem threeAdicDifferentOrderLeRamificationSubOne
    (hbound : ∀ σ : ThreeAdicIntegralInertia L, σ ≠ 1 →
      threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.val.toAlgHom) ≤ 1) :
    threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L)) ≤
      threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) - 1 := by
  classical
  rw [threeAdicDifferentOrderEqSumInertia]
  have hs := Finset.sum_le_sum (s := Finset.univ.erase (1 : ThreeAdicIntegralInertia L))
    (g := fun _ => 1) (fun σ hσ => hbound σ (Finset.mem_erase.mp hσ).1)
  simpa only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem
    (Finset.mem_univ (1 : ThreeAdicIntegralInertia L)), Finset.card_univ,
    ← Nat.card_eq_fintype_card, threeAdicInertiaCard] using hs

end ThreeAdicPlan
