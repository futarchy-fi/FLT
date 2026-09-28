/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalInertiaPolynomial

/-!
# Arithmetic of the critical inertia exponent

Every nonidentity inertia element has positive displacement. A displacement
larger than one therefore forces the different order to reach the ramification
index, placing the critical exponent in the Eisenstein perturbation range.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (L : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]
  {C : Type} [CommRing C] [Algebra ℤ_[3] C]
  [Algebra C (ThreeAdicIntegers L)] [IsScalarTower ℤ_[3] C (ThreeAdicIntegers L)]
  [Algebra.FormallyUnramified ℤ_[3] C]

/-- Every nonidentity inertia automorphism has positive displacement order. -/
theorem threeAdicInertiaDisplacementPositive (pc : PowerBasis ℤ_[3] C)
    (pb : PowerBasis C (ThreeAdicIntegers L))
    (σ : ThreeAdicIntegralInertia L) (hσ : σ ≠ 1) :
    0 < threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.val.toAlgHom) := by
  by_contra h
  have hz := Nat.eq_zero_of_not_pos h
  have hv := threeAdicAddValRelativeGenSubInertia L pc pb σ hσ
  rw [hz, Nat.cast_zero, IsDiscreteValuationRing.addVal_eq_zero_iff] at hv
  have hm := (Ideal.mem_inertia.mp σ.property) pb.gen
  change σ.val pb.gen - pb.gen ∈ IsLocalRing.maximalIdeal (ThreeAdicIntegers L) at hm
  have hn := (IsLocalRing.maximalIdeal (ThreeAdicIntegers L)).neg_mem hm
  simp only [neg_sub] at hn
  exact hn hv

/-- A displacement exceeding one forces the different order to be at least
the ramification index. -/
theorem threeAdicDifferentOrderGeRamificationOfWild [IsGalois ℚ_[3] L]
    (pc : PowerBasis ℤ_[3] C) (pb : PowerBasis C (ThreeAdicIntegers L))
    (c : ℕ) (hc : 1 < c)
    (hmax : ∃ σ : ThreeAdicIntegralInertia L, σ ≠ 1 ∧
      threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.val.toAlgHom) = c) :
    threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) ≤
      threeAdicIdealOrder L (differentIdeal ℤ_[3] (ThreeAdicIntegers L)) := by
  classical
  let H := ThreeAdicIntegralInertia L
  have hlt : (∑ σ ∈ Finset.univ.erase (1 : H), 1) <
      ∑ σ ∈ Finset.univ.erase (1 : H),
        threeAdicIdealOrder L (threeAdicDisplacementIdeal L σ.val.toAlgHom) := by
    apply Finset.sum_lt_sum
    · intro σ hσ
      exact threeAdicInertiaDisplacementPositive L pc pb σ (Finset.mem_erase.mp hσ).1
    · obtain ⟨σ, hσ, hk⟩ := hmax
      exact ⟨σ, Finset.mem_erase.mpr ⟨hσ, Finset.mem_univ _⟩, hk ▸ hc⟩
  have he : Fintype.card H =
      threeAdicIdealOrder L (Ideal.span {(3 : ThreeAdicIntegers L)}) :=
    (show Nat.card H = Fintype.card H from Nat.card_eq_fintype_card).symm.trans
      (threeAdicInertiaCard L)
  have hd := threeAdicDifferentOrderEqSumInertia L
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem
    (Finset.mem_univ (1 : H)), Finset.card_univ, he] at hlt
  rw [← hd] at hlt
  omega

end ThreeAdicPlan
