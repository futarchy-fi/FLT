/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.AugmentedFontaineBound
public import FLT.GaloisRepresentation.HardlyRamified.CategoryDPointCharacters

/-!
# Simple category-D objects under the local Fontaine hypothesis

The local Fontaine different bound supplies the augmented discriminant estimate.
Consequently the augmented field is sextic, and the simple object's generic
character has the existing order-three classification.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- Fontaine's local bound forces the augmented field to have degree six. -/
theorem augmentedField_finrank_eq_six_of_fontaine
    (hF : FontaineDifferentBoundKilledThree)
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    Module.finrank ℚ (AugmentedField H) = 6 :=
  augmentedField_finrank_eq_six_of_discriminantBound hs hD
    (augmentedDiscriminantBound_of_fontaine hF hs hD)

/-- Fontaine's local bound makes the canonical Kummer embedding bijective. -/
theorem kummerTwoFieldToAugmentedField_bijective_of_fontaine
    (hF : FontaineDifferentBoundKilledThree)
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    Function.Bijective (kummerTwoFieldToAugmentedField H) :=
  kummerTwoFieldToAugmentedField_bijective_of_discriminantBound hs hD
    (augmentedDiscriminantBound_of_fontaine hF hs hD)

/-- Under Fontaine's local bound the augmented field is its sextic Kummer subfield. -/
def kummerTwoAugmentedFieldEquivOfFontaine
    (hF : FontaineDifferentBoundKilledThree)
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    K₀ ≃ₐ[ℚ] AugmentedField H :=
  kummerTwoAugmentedFieldEquivOfDiscriminantBound hs hD
    (augmentedDiscriminantBound_of_fontaine hF hs hD)

/-- Fontaine's local bound supplies the normal three-subgroup of the augmented quotient. -/
theorem augmentedPointGaloisGroup_normal_threeSubgroup_of_fontaine
    (hF : FontaineDifferentBoundKilledThree)
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    ∃ P : Subgroup (AugmentedPointGaloisGroup H),
      P.Normal ∧ IsPGroup 3 P ∧ Nat.card (AugmentedPointGaloisGroup H ⧸ P) = 2 :=
  augmentedPointGaloisGroup_normal_threeSubgroup hs hD
    (augmentedDiscriminantBound_of_fontaine hF hs hD)

/-- Under Fontaine's local bound a simple category-D object's points have
dimension one over `ZMod 3`, with a character valued in the two signs. -/
theorem Simple.points_three_of_fontaine
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H)
    (hF : FontaineDifferentBoundKilledThree) (hD : InCategoryD H) :
    letI _threeModule := hs.threeModule hD
    Module.finrank (ZMod 3) H.points = 1 ∧
      ∃ χ : Γ →* (ZMod 3)ˣ,
        (∀ σ, χ σ = 1 ∨ χ σ = -1) ∧
        (∀ (σ : Γ) (w : H.points), σ • w = (χ σ : ZMod 3) • w) :=
  hs.points_three_of_discriminantBound hD (augmentedDiscriminantBound_of_fontaine hF hs hD)

/-- Under Fontaine's local bound the simple object's point character is
trivial or the mod-three cyclotomic character. -/
theorem Simple.point_character_of_fontaine
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H)
    (hF : FontaineDifferentBoundKilledThree) (hD : InCategoryD H) :
    letI _threeModule := hs.threeModule hD
    Module.finrank (ZMod 3) H.points = 1 ∧
      ∃ χ : Γ →* (ZMod 3)ˣ, (χ = 1 ∨ χ = modThreeCyclotomic) ∧
        ∀ (σ : Γ) (w : H.points), σ • w = (χ σ : ZMod 3) • w :=
  hs.point_character_of_discriminantBound hD
    (augmentedDiscriminantBound_of_fontaine hF hs hD)

end ThreeAdicPlan
