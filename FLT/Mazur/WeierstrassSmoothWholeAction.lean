/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothGroup
public import FLT.Mazur.WeierstrassLeftSmoothIdentity
public import FLT.Mazur.WeierstrassLeftSmoothAssociativity
public import FLT.Mazur.WeierstrassLeftSmoothRestriction

/-!
# The smooth Weierstrass group acts on the whole original cubic

The constructed smooth-by-whole addition is an action in the category over
the original coefficient spectrum. Its unit, associativity, and restriction
laws hold without a discriminant-unit assumption.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
local notation "G" => Grp.X (CommGrp.toGrp (integralSmoothGroup W))
local notation "E" => integralCurveOver W

/-- The entire original cubic receives the constructed smooth-group action. -/
def integralSmoothWholeAction : (G) ⊗ (E) ⟶ (E) :=
  Over.homMk (leftSmoothFactorAddition W) (leftSmoothFactorAddition_structure W)

/-- The categorical unit pairing is the original zero pairing of smooth and whole inputs. -/
theorem integralSmoothWholeAction_zeroPair :
    (λ_ (E)).inv.left ≫ (η[(G)] ▷ (E)).left = leftSmoothFactorZero W := by
  apply pullback.hom_ext
  · rw [Category.assoc, Over.whiskerRight_left_fst, ← Category.assoc]
    exact (congrArg (fun f ↦ f ≫ (integralSmoothZero W))
      (Over.leftUnitor_inv_left_fst (E))).trans (leftSmoothFactorZero_fst W).symm
  · rw [Category.assoc, Over.whiskerRight_left_snd]
    exact (Over.leftUnitor_inv_left_snd (E)).trans (leftSmoothFactorZero_snd W).symm

/-- The smooth identity acts trivially on the entire original cubic. -/
theorem integralSmoothWholeAction_unit :
    η[(G)] ▷ (E) ≫ integralSmoothWholeAction W = (λ_ (E)).hom := by
  apply (cancel_epi (λ_ (E)).inv).mp
  apply Over.OverMorphism.ext
  change (_ ≫ _) ≫ leftSmoothFactorAddition W = _
  rw [integralSmoothWholeAction_zeroPair, leftSmoothFactorAddition_left_identity]
  exact congrArg Over.Hom.left (Iso.inv_hom_id (λ_ (E))).symm

/-- Multiplication on the first two factors gives the original left-associated pair. -/
theorem integralSmoothWholeAction_firstPair :
    (μ[(G)] ▷ (E)).left = leftSmoothAddFirstPair W := by
  apply pullback.hom_ext
  · exact (Over.whiskerRight_left_fst _).trans (leftSmoothAddFirstPair_fst W).symm
  · exact (Over.whiskerRight_left_snd _).trans (leftSmoothAddFirstPair_snd W).symm

/-- The categorical associator retains the original last two inputs. -/
theorem integralSmoothWholeAction_lastPair :
    (α_ (G) (G) (E)).hom.left ≫ pullback.snd _ _ = leftSmoothTripleLastPair W := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    exact (Over.associator_hom_left_snd_fst _ _ _).trans
      (leftSmoothTripleLastPair_fst W).symm
  · rw [Category.assoc]
    exact (Over.associator_hom_left_snd_snd _ _ _).trans
      (leftSmoothTripleLastPair_snd W).symm

/-- Acting on the last pair gives the original right-associated pair. -/
theorem integralSmoothWholeAction_lastSum :
    (α_ (G) (G) (E)).hom.left ≫ ((G) ◁ integralSmoothWholeAction W).left =
      leftSmoothAddLastPair W := by
  apply pullback.hom_ext
  · rw [Category.assoc, Over.whiskerLeft_left_fst]
    exact (Over.associator_hom_left_fst _ _ _).trans (leftSmoothAddLastPair_fst W).symm
  · rw [Category.assoc, Over.whiskerLeft_left_snd, ← Category.assoc]
    exact (congrArg (fun f ↦ f ≫ leftSmoothFactorAddition W)
      (integralSmoothWholeAction_lastPair W)).trans (leftSmoothAddLastPair_snd W).symm

/-- The whole action is associative, including on singular fibers and nonreduced tests. -/
theorem integralSmoothWholeAction_assoc :
    μ[(G)] ▷ (E) ≫ integralSmoothWholeAction W =
      (α_ (G) (G) (E)).hom ≫ (G) ◁ integralSmoothWholeAction W ≫
        integralSmoothWholeAction W := by
  apply Over.OverMorphism.ext
  change (μ[(G)] ▷ (E)).left ≫ leftSmoothFactorAddition W = _
  rw [integralSmoothWholeAction_firstPair]
  change _ = _ ≫ _ ≫ leftSmoothFactorAddition W
  rw [← Category.assoc, integralSmoothWholeAction_lastSum]
  exact leftSmoothFactorAddition_assoc W

/-- The smooth group embeds in the original whole cubic by its actual smooth open. -/
def integralSmoothWholeInclusion : (G) ⟶ (E) :=
  Over.homMk (integralSmoothOpen W).ι rfl

/-- The action restricts to the original smooth-group multiplication. -/
theorem integralSmoothWholeAction_restriction :
    (G) ◁ integralSmoothWholeInclusion W ≫ integralSmoothWholeAction W =
      μ[(G)] ≫ integralSmoothWholeInclusion W := by
  have hp : ((G) ◁ integralSmoothWholeInclusion W).left =
      smoothFactorsToLeftSmooth W := by
    apply pullback.hom_ext
    · exact (Over.whiskerLeft_left_fst _).trans (smoothFactorsToLeftSmooth_fst W).symm
    · exact (Over.whiskerLeft_left_snd _).trans (smoothFactorsToLeftSmooth_snd W).symm
  apply Over.OverMorphism.ext
  change ((G) ◁ integralSmoothWholeInclusion W).left ≫ leftSmoothFactorAddition W = _
  rw [hp]
  exact smoothFactorsToLeftSmooth_addition W

end FLT.Mazur.WeierstrassIntegralChart
