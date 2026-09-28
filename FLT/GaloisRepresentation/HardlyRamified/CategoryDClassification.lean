/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.CategoryDFontaine
public import FLT.GaloisRepresentation.HardlyRamified.CategoryDIntegralFontaine
public import FLT.GroupScheme.FontaineDifferentBound

/-!
# Classification of simple category-D objects

Fontaine's strict local different bound supplies the augmented discriminant
estimate unconditionally. The augmented field is the sextic Kummer field, and
each simple category-D object is the constant-three or cube-root model.
The universally quantified discriminant bound is also available as the input
to integral sorting.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- Every simple category-D object satisfies the augmented discriminant estimate. -/
theorem augmentedDiscriminantBound
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    AugmentedDiscriminantBound H :=
  augmentedDiscriminantBound_of_fontaine fontaineDifferentBoundKilledThree hs hD

/-- The universally quantified discriminant estimate required by integral sorting. -/
theorem hdisc : ∀ A : FiniteFlatObject ZInvTwo,
    Simple A → InCategoryD A → AugmentedDiscriminantBound A :=
  fun _ hs hD ↦ augmentedDiscriminantBound hs hD

/-- The augmented field of a simple category-D object has degree six. -/
theorem augmentedFieldFinrankEqSix
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    Module.finrank ℚ (AugmentedField H) = 6 :=
  augmentedField_finrank_eq_six_of_fontaine fontaineDifferentBoundKilledThree hs hD

/-- The canonical Kummer embedding into the augmented field is bijective. -/
theorem kummerTwoFieldToAugmentedFieldBijective
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    Function.Bijective (kummerTwoFieldToAugmentedField H) :=
  kummerTwoFieldToAugmentedField_bijective_of_fontaine
    fontaineDifferentBoundKilledThree hs hD

/-- The augmented field of a simple category-D object is its sextic Kummer subfield. -/
def kummerTwoAugmentedFieldEquiv
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    K₀ ≃ₐ[ℚ] AugmentedField H :=
  kummerTwoAugmentedFieldEquivOfFontaine fontaineDifferentBoundKilledThree hs hD

/-- The augmented point quotient has a normal three-subgroup of index two. -/
theorem augmentedPointGaloisGroupNormalThreeSubgroup
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    ∃ P : Subgroup (AugmentedPointGaloisGroup H),
      P.Normal ∧ IsPGroup 3 P ∧ Nat.card (AugmentedPointGaloisGroup H ⧸ P) = 2 :=
  augmentedPointGaloisGroup_normal_threeSubgroup_of_fontaine
    fontaineDifferentBoundKilledThree hs hD

/-- A simple category-D object's points have dimension one over `ZMod 3`,
with Galois action given by a character valued in the two signs. -/
theorem Simple.pointsThree
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    letI _instThreeModule := hs.threeModule hD
    Module.finrank (ZMod 3) H.points = 1 ∧
      ∃ χ : Γ →* (ZMod 3)ˣ,
        (∀ σ, χ σ = 1 ∨ χ σ = -1) ∧
        (∀ (σ : Γ) (w : H.points), σ • w = (χ σ : ZMod 3) • w) :=
  hs.points_three_of_fontaine fontaineDifferentBoundKilledThree hD

/-- The point character of a simple category-D object is trivial or cyclotomic. -/
theorem Simple.pointCharacter
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    letI _instThreeModule := hs.threeModule hD
    Module.finrank (ZMod 3) H.points = 1 ∧
      ∃ χ : Γ →* (ZMod 3)ˣ, (χ = 1 ∨ χ = modThreeCyclotomic) ∧
        ∀ (σ : Γ) (w : H.points), σ • w = (χ σ : ZMod 3) • w :=
  hs.point_character_of_fontaine fontaineDifferentBoundKilledThree hD

/-- A simple category-D object is integrally isomorphic to the constant-three
or cube-root model. -/
theorem Simple.integralModel
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H) :
    Nonempty (H.Iso constantThree) ∨ Nonempty (H.Iso muThree) :=
  hs.integral_model_of_fontaine fontaineDifferentBoundKilledThree hD

/-- The integral order-three classification of simple category-D objects. -/
theorem simpleDThree
    (H : FiniteFlatObject ZInvTwo) (hs : Simple H) (hD : InCategoryD H) :
    Nonempty (H.Iso constantThree) ∨ Nonempty (H.Iso muThree) :=
  hs.integralModel hD

end ThreeAdicPlan
