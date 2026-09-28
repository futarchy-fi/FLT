/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AugmentedFieldData
public import FLT.GaloisRepresentation.HardlyRamified.AugmentedFieldUnramifiedTwo
public import FLT.GaloisRepresentation.HardlyRamified.KummerTwoDyadic

/-!
# The augmented field is unramified over the Kummer field outside three

The finite flat model supplies absolute unramifiedness away from two and
three. At two the Kummer subfield accounts for the entire ramification index.
Together these give the arithmetic hypothesis of the no-quadratic-extension
theorem over `K₀`.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

open NumberField

/-- Relative unramifiedness outside three for the canonical embedding of `K₀`
into the augmented point field of a simple category-D object. -/
theorem augmentedField_unramifiedOutsideThree {H : FiniteFlatObject ZInvTwo}
    (hs : Simple H) (hD : InCategoryD H) :
    letI : Algebra K₀ (AugmentedField H) := (kummerTwoFieldToAugmentedField H).toAlgebra
    KummerTwoUnramifiedOutsideThree (AugmentedField H) := by
  let : Algebra K₀ (AugmentedField H) := (kummerTwoFieldToAugmentedField H).toAlgebra
  intro Q _ hQ hQthree P _ _
  have : NeZero Q := ⟨hQ⟩
  let p := Ideal.absNorm (Q.under ℤ)
  have hp : p.Prime := Nat.absNorm_under_prime Q
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := Int.liesOver_span_absNorm Q
  have : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.LiesOver.trans P Q (Ideal.span {(p : ℤ)})
  have hp3 : p ≠ 3 := by
    intro hp3
    have : Q.LiesOver (Ideal.span {(3 : ℤ)}) := by
      simpa only [hp3, Nat.cast_ofNat] using
        (inferInstance : Q.LiesOver (Ideal.span {(p : ℤ)}))
    apply hQthree
    have hmem : Q ∈ (Ideal.span {(3 : ℤ)}).primesOver (𝓞 K₀) :=
      ⟨inferInstance, inferInstance⟩
    rw [uniquePrimeAboveThree_kummerTwoField] at hmem
    exact Set.mem_singleton_iff.mp hmem
  by_cases hp2 : p = 2
  · have : P.LiesOver (Ideal.span {(2 : ℤ)}) := by
      simpa only [hp2, Nat.cast_ofNat] using
        (inferInstance : P.LiesOver (Ideal.span {(p : ℤ)}))
    exact augmentedField_isUnramifiedAt_two hs hD P
  · have : P.LiesOver hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal :=
      liesOver_ratPrime_of_liesOver_int P hp
    have : Algebra.IsUnramifiedAt (𝓞 ℚ) P :=
      augmentedField_isUnramifiedIn hs hD p hp (by simp [hp2, hp3]) P
        inferInstance inferInstance
    exact Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 ℚ) P

/-- The augmented field cannot be a quadratic extension of its Kummer subfield. -/
theorem augmentedField_finrank_kummerTwo_ne_two {H : FiniteFlatObject ZInvTwo}
    (hs : Simple H) (hD : InCategoryD H) :
    letI : Algebra K₀ (AugmentedField H) := (kummerTwoFieldToAugmentedField H).toAlgebra
    Module.finrank K₀ (AugmentedField H) ≠ 2 := by
  let : Algebra K₀ (AugmentedField H) := (kummerTwoFieldToAugmentedField H).toAlgebra
  exact no_quadratic_extension_auxiliary (AugmentedField H)
    (augmentedField_unramifiedOutsideThree hs hD)

end ThreeAdicPlan
