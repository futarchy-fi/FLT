/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AugmentedFieldUnramified
public import FLT.GaloisRepresentation.HardlyRamified.ThreeAdicDegree

/-!
# Conditional identification of the augmented field

The Fontaine discriminant estimate remains an explicit hypothesis. Given it,
Odlyzko's degree bound and relative unramifiedness identify the augmented field
with its canonical sextic Kummer subfield.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

/-- The discriminant estimate needed to identify the augmented field. -/
def AugmentedDiscriminantBound (H : FiniteFlatObject ZInvTwo) : Prop :=
  |(NumberField.discr (AugmentedField H) : ℝ)| ≤
    ((2 : ℝ) ^ (2 / 3 : ℝ) * (3 : ℝ) ^ (3 / 2 : ℝ)) ^
      Module.finrank ℚ (AugmentedField H)

/-- The canonical Kummer subfield forces the augmented degree to be divisible by six. -/
theorem six_dvd_finrank_augmentedField (H : FiniteFlatObject ZInvTwo) :
    6 ∣ Module.finrank ℚ (AugmentedField H) := by
  let : Algebra K₀ (AugmentedField H) := (kummerTwoFieldToAugmentedField H).toAlgebra
  have ht := Module.finrank_mul_finrank ℚ K₀ (AugmentedField H)
  rw [finrank_kummerTwoField] at ht
  exact ⟨Module.finrank K₀ (AugmentedField H), ht.symm⟩

/-- Under the explicit discriminant estimate the augmented field has degree six. -/
theorem augmentedField_finrank_eq_six_of_discriminantBound
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (hdisc : AugmentedDiscriminantBound H) : Module.finrank ℚ (AugmentedField H) = 6 := by
  let : Algebra K₀ (AugmentedField H) := (kummerTwoFieldToAugmentedField H).toAlgebra
  rcases auxiliary_degree_eq_six_or_twelve (AugmentedField H)
    (six_dvd_finrank_augmentedField H) hdisc with h6 | h12
  · exact h6
  · have ht := Module.finrank_mul_finrank ℚ K₀ (AugmentedField H)
    rw [finrank_kummerTwoField, h12] at ht
    have hne := augmentedField_finrank_kummerTwo_ne_two hs hD
    omega

/-- The canonical Kummer embedding is surjective under the discriminant estimate. -/
theorem kummerTwoFieldToAugmentedField_bijective_of_discriminantBound
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (hdisc : AugmentedDiscriminantBound H) :
    Function.Bijective (kummerTwoFieldToAugmentedField H) := by
  let : Algebra K₀ (AugmentedField H) := (kummerTwoFieldToAugmentedField H).toAlgebra
  have ht := Module.finrank_mul_finrank ℚ K₀ (AugmentedField H)
  rw [finrank_kummerTwoField,
    augmentedField_finrank_eq_six_of_discriminantBound hs hD hdisc] at ht
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mp (by omega)

/-- The augmented field equals its sextic Kummer subfield, conditional on the
explicit discriminant estimate. -/
def kummerTwoAugmentedFieldEquivOfDiscriminantBound
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (hdisc : AugmentedDiscriminantBound H) : K₀ ≃ₐ[ℚ] AugmentedField H :=
  AlgEquiv.ofBijective (kummerTwoFieldToAugmentedField H)
    (kummerTwoFieldToAugmentedField_bijective_of_discriminantBound hs hD hdisc)

end ThreeAdicPlan
