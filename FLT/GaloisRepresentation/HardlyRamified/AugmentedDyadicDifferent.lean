/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AugmentedDiscriminantReduction
public import FLT.GaloisRepresentation.HardlyRamified.KummerTwoDifferent
public import FLT.NumberField.DifferentTower

/-!
# The dyadic different of the augmented field

The sextic Kummer subfield has dyadic different exponent two and ramification
index three. Relative unramifiedness transfers both numbers to the augmented
field. Consequently the discriminant reduction now needs only the global
normalized different bound at three; the tame input at two is proved here.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

open NumberField

/-- Any extension unramified over the Kummer field at a dyadic prime has
absolute different exponent two and absolute ramification index three there. -/
theorem kummerTwo_dyadic_different_of_isUnramifiedAt
    (L : Type*) [Field L] [NumberField L] [Algebra K₀ L]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(2 : ℤ)})]
    [Algebra.IsUnramifiedAt (𝓞 K₀) P] :
    differentExponentAt L P = 2 ∧ P.ramificationIdx ℤ = 3 := by
  let Q := P.under (𝓞 K₀)
  have : Q.LiesOver (Ideal.span {(2 : ℤ)}) :=
    Ideal.LiesOver.tower_bot P Q (Ideal.span {(2 : ℤ)})
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(2 : ℤ)}) (by simp) P
  constructor
  · rw [differentExponentAt_eq_of_isUnramifiedAt K₀ L P hP]
    exact differentExponentAt_kummerTwoField_two Q
  · rw [Ideal.ramificationIdx_tower (R := ℤ) Q P,
      ramificationIdx_at_two Q, Ideal.ramificationIdx_eq_one P (𝓞 K₀), mul_one]

/-- The augmented field has dyadic different exponent two and ramification index three. -/
theorem augmentedField_dyadic_different
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (P : Ideal (𝓞 (AugmentedField H))) [P.IsPrime]
    (hP : (2 : 𝓞 (AugmentedField H)) ∈ P) :
    differentExponentAt (AugmentedField H) P = 2 ∧ P.ramificationIdx ℤ = 3 := by
  let : Algebra K₀ (AugmentedField H) := (kummerTwoFieldToAugmentedField H).toAlgebra
  have : P.LiesOver (Ideal.span {(2 : ℤ)}) :=
    (Ideal.liesOver_span_iff (Ideal.IsPrime.ne_top inferInstance)
      (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 2))).mpr
        (by simpa only [map_natCast, Nat.cast_ofNat, map_ofNat] using hP)
  have : Algebra.IsUnramifiedAt (𝓞 K₀) P := augmentedField_isUnramifiedAt_two hs hD P
  exact kummerTwo_dyadic_different_of_isUnramifiedAt (AugmentedField H) P

/-- The tame different formula at two for the augmented field. -/
theorem augmentedField_differentExponentAt_eq_ramificationIdx_sub_one
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (P : Ideal (𝓞 (AugmentedField H))) [P.IsPrime]
    (hP : (2 : 𝓞 (AugmentedField H)) ∈ P) :
    differentExponentAt (AugmentedField H) P = P.ramificationIdx ℤ - 1 := by
  obtain ⟨hd, he⟩ := augmentedField_dyadic_different hs hD P hP
  rw [hd, he]

/-- After the dyadic calculation, only the normalized global bound at three
remains as an input to the augmented discriminant bound. -/
theorem augmentedDiscriminantBound_of_three_bound
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (hthree : ∀ (P : Ideal (𝓞 (AugmentedField H))) [P.IsPrime],
      (3 : 𝓞 (AugmentedField H)) ∈ P →
        normalizedDifferentExponentAt (AugmentedField H) P < (3 / 2 : ℚ)) :
    AugmentedDiscriminantBound H :=
  augmentedDiscriminantBound_of_tame_different_and_three_bound hs hD
    (augmentedField_differentExponentAt_eq_ramificationIdx_sub_one hs hD) hthree

end ThreeAdicPlan
