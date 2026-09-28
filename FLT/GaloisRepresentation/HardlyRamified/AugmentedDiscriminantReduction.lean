/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AugmentedFieldDegree
public import FLT.NumberField.DifferentExponentBounds

/-!
# The global part of the augmented discriminant reduction

The augmented field is already known to be unramified away from two and
three and to have dyadic ramification index dividing three. Here those
facts are combined with explicit primewise different bounds.

The last theorem still requires the tame different formula at two and a
bound for the global different exponent at three. Relating the latter to
`FontaineDifferentBoundKilledThree` requires a completion comparison
and a finite flat model realizing that completed point field; neither is
silently included in the local Fontaine hypothesis.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

open NumberField

/-- Absolute unramifiedness away from two and three, stated over `ℤ` and
using membership in prime ideals rather than rational places. -/
theorem augmentedField_isUnramifiedAt_int_of_not_mem_two_three
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (P : Ideal (𝓞 (AugmentedField H))) [P.IsPrime]
    (h2 : (2 : 𝓞 (AugmentedField H)) ∉ P)
    (h3 : (3 : 𝓞 (AugmentedField H)) ∉ P) : Algebra.IsUnramifiedAt ℤ P := by
  by_cases hP : P = ⊥
  · subst P
    apply not_dvd_differentIdeal_iff.mp
    simpa only [← Ideal.zero_eq_bot, zero_dvd_iff] using
      (differentIdeal_ne_bot : differentIdeal ℤ (𝓞 (AugmentedField H)) ≠ ⊥)
  have : NeZero P := ⟨hP⟩
  let p := Ideal.absNorm (P.under ℤ)
  have hp : p.Prime := Nat.absNorm_under_prime P
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := Int.liesOver_span_absNorm P
  have hpmem : (p : 𝓞 (AugmentedField H)) ∈ P := by
    have hm := (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top inferInstance)
      (Nat.prime_iff_prime_int.mp hp)).mp
        (inferInstance : P.LiesOver (Ideal.span {(p : ℤ)}))
    simpa only [map_natCast] using hm
  have hp2 : p ≠ 2 := by
    intro heq
    apply h2
    simpa only [heq, Nat.cast_ofNat] using hpmem
  have hp3 : p ≠ 3 := by
    intro heq
    apply h3
    simpa only [heq, Nat.cast_ofNat] using hpmem
  have : P.LiesOver hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal :=
    liesOver_ratPrime_of_liesOver_int P hp
  have : Algebra.IsUnramifiedAt (𝓞 ℚ) P :=
    augmentedField_isUnramifiedIn hs hD p hp (by simp [hp2, hp3]) P
      inferInstance inferInstance
  have : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
    Algebra.FormallyUnramified.of_equiv Rat.ringOfIntegersEquiv.symm.toIntAlgEquiv
  exact Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime P)

/-- The global discriminant estimate follows from bounds for the actual
different ideal at the two exceptional primes. -/
theorem augmentedDiscriminantBound_of_differentExponent_bounds
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (h2 : ∀ (P : Ideal (𝓞 (AugmentedField H))) [P.IsPrime],
      (2 : 𝓞 (AugmentedField H)) ∈ P →
        3 * differentExponentAt (AugmentedField H) P ≤ 2 * P.ramificationIdx ℤ)
    (h3 : ∀ (P : Ideal (𝓞 (AugmentedField H))) [P.IsPrime],
      (3 : 𝓞 (AugmentedField H)) ∈ P →
        2 * differentExponentAt (AugmentedField H) P ≤ 3 * P.ramificationIdx ℤ) :
    AugmentedDiscriminantBound H :=
  discr_le_fontaine_of_differentExponent_bounds (AugmentedField H) h2 h3
    (augmentedField_isUnramifiedAt_int_of_not_mem_two_three hs hD)

/-- The remaining local inputs can be stated as the tame different formula
at two and the normalized global different bound at three. The dyadic
ramification-index condition and all other primes are discharged here. -/
theorem augmentedDiscriminantBound_of_tame_different_and_three_bound
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (htame : ∀ (P : Ideal (𝓞 (AugmentedField H))) [P.IsPrime],
      (2 : 𝓞 (AugmentedField H)) ∈ P →
        differentExponentAt (AugmentedField H) P = P.ramificationIdx ℤ - 1)
    (hthree : ∀ (P : Ideal (𝓞 (AugmentedField H))) [P.IsPrime],
      (3 : 𝓞 (AugmentedField H)) ∈ P →
        normalizedDifferentExponentAt (AugmentedField H) P < (3 / 2 : ℚ)) :
    AugmentedDiscriminantBound H := by
  apply augmentedDiscriminantBound_of_differentExponent_bounds hs hD
  · intro P _ hP
    have : P.LiesOver (Ideal.span {(2 : ℤ)}) :=
      (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top inferInstance)
        (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 2))).mpr
          (by simpa only [map_natCast, Nat.cast_ofNat, map_ofNat] using hP)
    have : P.LiesOver twoAdicPlace.asIdeal :=
      liesOver_ratPrime_of_liesOver_int P (by decide : Nat.Prime 2)
    apply three_mul_differentExponentAt_le_of_eq_ramificationIdx_sub_one
      (AugmentedField H) P _ (htame P hP)
    rw [ramificationIdx_int_eq_ratIntegers]
    exact augmentedField_ramificationIdx_dvd_three hs hD P
  · intro P _ hP
    exact two_mul_differentExponentAt_le_of_normalized_lt
      (AugmentedField H) P (hthree P hP)

end ThreeAdicPlan
