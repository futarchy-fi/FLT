/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AugmentedField
public import FLT.GaloisRepresentation.HardlyRamified.RationalRamificationBridge

/-!
# Relative dyadic unramifiedness of the augmented field

The sextic Kummer field already accounts for all ramification at two: its
absolute ramification index is three, and that of the augmented field divides
three. Multiplicativity forces the relative ramification index to be one.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

open NumberField

/-- In an extension of `K₀`, an absolute dyadic index dividing three implies
relative unramifiedness. -/
theorem kummerTwo_isUnramifiedAt_two_of_ramificationIdx_dvd_three
    {L : Type*} [Field L] [NumberField L] [Algebra K₀ L]
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(2 : ℤ)})]
    (he : P.ramificationIdx ℤ ∣ 3) : Algebra.IsUnramifiedAt (𝓞 K₀) P := by
  let Q := P.under (𝓞 K₀)
  have : Q.LiesOver (Ideal.span {(2 : ℤ)}) :=
    Ideal.LiesOver.tower_bot P Q (Ideal.span {(2 : ℤ)})
  have ht := Ideal.ramificationIdx_tower (R := ℤ) Q P
  rw [ramificationIdx_at_two Q] at ht
  have hpos := P.ramificationIdx_pos (𝓞 K₀)
  apply Ideal.ramificationIdx_eq_one_iff.mp
  have hle := Nat.le_of_dvd (by decide : 0 < 3) he
  omega

/-- Every dyadic prime of the augmented field is unramified over the embedded
sextic Kummer field. -/
theorem augmentedField_isUnramifiedAt_two {H : FiniteFlatObject ZInvTwo}
    (hs : Simple H) (hD : InCategoryD H) :
    letI : Algebra K₀ (AugmentedField H) := (kummerTwoFieldToAugmentedField H).toAlgebra
    ∀ (P : Ideal (𝓞 (AugmentedField H))) [P.IsPrime]
      [P.LiesOver (Ideal.span {(2 : ℤ)})], Algebra.IsUnramifiedAt (𝓞 K₀) P := by
  let : Algebra K₀ (AugmentedField H) := (kummerTwoFieldToAugmentedField H).toAlgebra
  intro P _ _
  have : P.LiesOver twoAdicPlace.asIdeal :=
    liesOver_ratPrime_of_liesOver_int P (by decide : Nat.Prime 2)
  apply kummerTwo_isUnramifiedAt_two_of_ramificationIdx_dvd_three P
  rw [ramificationIdx_int_eq_ratIntegers]
  exact augmentedField_ramificationIdx_dvd_three hs hD P

end ThreeAdicPlan
