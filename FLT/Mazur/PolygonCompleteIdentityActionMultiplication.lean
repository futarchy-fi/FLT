/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityMultiplicationCubic
public import FLT.Mazur.WeierstrassLeftSmoothRestriction

/-!
# The whole-domain cubic target agrees with original identity multiplication

Include the original identity product in the original whole action domain.
The constructed cubic target there is the contraction of actual multiplication.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "G" => completePointOriginalBaseGroup K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "U" => completePointIdentityOpen K n h i
local notation "π" => exactVeroneseProjToBase K n h
local notation "g" => completePointToIntegralCubic K n h i

/-- The original identity pair included in the entire original action domain. -/
def completeIdentityPairToAction :
    ((G).X ⊗ (G).X).left ⟶ completeIdentityActionProduct K n h i :=
  pullback.lift (pullback.fst (G).X.hom (G).X.hom)
    (pullback.snd (G).X.hom (G).X.hom ≫ (U).ι) (by
      rw [Category.assoc, ← completePointOriginalBaseGroup_structure]
      exact pullback.condition)

/-- The inclusion retains the first identity parameter. -/
@[reassoc] theorem completeIdentityPairToAction_fst :
    completeIdentityPairToAction K n h i ≫ pullback.fst (G).X.hom (π) =
      pullback.fst (G).X.hom (G).X.hom := pullback.lift_fst _ _ _

/-- Its second coordinate is the original identity-open inclusion. -/
@[reassoc] theorem completeIdentityPairToAction_snd :
    completeIdentityPairToAction K n h i ≫ pullback.snd (G).X.hom (π) =
      pullback.snd (G).X.hom (G).X.hom ≫ (U).ι := pullback.lift_snd _ _ _

/-- Both routes use the same original pair of cubic inputs. -/
theorem completeIdentityPairToAction_cubicPair :
    completeIdentityPairToAction K n h i ≫ completeIdentityActionToCubicProduct K n h i =
      completeIdentitySmoothPair K n h i ≫ smoothFactorsToLeftSmooth (W) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeIdentityActionToCubicProduct_fst,
      completeIdentityPairToAction_fst_assoc, smoothFactorsToLeftSmooth_fst,
      completeIdentitySmoothPair_fst]
  · simp only [Category.assoc, completeIdentityActionToCubicProduct_snd,
      completeIdentityPairToAction_snd_assoc, smoothFactorsToLeftSmooth_snd,
      completeIdentitySmoothPair_snd_assoc, completePointSmoothCubicIso_inclusion]

/-- Original identity multiplication contracts to the entire-domain cubic action target. -/
@[reassoc] theorem completeIdentityPairToAction_target :
    completeIdentityPairToAction K n h i ≫ completeIdentityActionTarget K n h i =
      (μ[(G).X]).left ≫ (U).ι ≫ (g) := by
  rw [completeIdentityActionTarget, ← Category.assoc,
    completeIdentityPairToAction_cubicPair, Category.assoc,
    smoothFactorsToLeftSmooth_addition, ← Category.assoc,
    ← completeIdentitySmoothPair_addition, Category.assoc,
    completePointSmoothCubicIso_inclusion]

end FLT.Mazur.PolygonInfinitesimalStages
