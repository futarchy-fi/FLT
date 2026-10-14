/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginalBaseGroup
public import FLT.Mazur.WeierstrassLeftSmoothInverseAction

/-!
# The original identity parameter acting into the contracted cubic

Construct the cubic-valued map on the entire original identity-by-polygon
product. Its second input includes every contracted component. This is the
map to lift through the original contraction, not yet a polygon-valued action.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "G" => completePointOriginalBaseGroup K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "π" => exactVeroneseProjToBase K n h
local notation "e" => completePointSmoothCubicIso K n h i

/-- The original identity group times the whole original polygon over its unchanged base. -/
abbrev completeIdentityActionProduct : Scheme := pullback (G).X.hom (π)

/-- The identity comparison retains the literal original base map. -/
@[reassoc] theorem completeIdentityActionParameter_structure :
    (e).hom ≫ integralSmoothStructure (W) = (G).X.hom ≫ (S).toSpecΓ := by
  rw [completePointOriginalBaseGroup_structure]
  change (e).hom ≫ (integralSmoothOpen (W)).ι ≫ integralCurveStructure (W) = _
  rw [completePointSmoothCubicIso_inclusion_assoc, Category.assoc,
    completePointToIntegralCubic_over]

/-- Both original inputs give the actual smooth-by-whole cubic input pair. -/
def completeIdentityActionToCubicProduct :
    completeIdentityActionProduct K n h i ⟶ leftSmoothFactorProduct (W) :=
  pullback.lift (pullback.fst (G).X.hom (π) ≫ (e).hom)
    (pullback.snd (G).X.hom (π) ≫ (g)) (by
      simp only [Category.assoc, completeIdentityActionParameter_structure,
        completePointToIntegralCubic_over]
      simpa only [Category.assoc] using
        congrArg (fun f ↦ f ≫ (S).toSpecΓ)
          (show pullback.fst (G).X.hom (π) ≫ (G).X.hom =
            pullback.snd (G).X.hom (π) ≫ (π) from pullback.condition))

/-- The comparison retains the original identity parameter. -/
@[reassoc] theorem completeIdentityActionToCubicProduct_fst :
    completeIdentityActionToCubicProduct K n h i ≫ pullback.fst _ _ =
      pullback.fst (G).X.hom (π) ≫ (e).hom := pullback.lift_fst _ _ _

/-- The comparison retains the original full contraction as its second coordinate. -/
@[reassoc] theorem completeIdentityActionToCubicProduct_snd :
    completeIdentityActionToCubicProduct K n h i ≫ pullback.snd _ _ =
      pullback.snd (G).X.hom (π) ≫ (g) := pullback.lift_snd _ _ _

/-- The actual contraction-side action, defined even on all original exceptional inputs. -/
def completeIdentityActionTarget :
    completeIdentityActionProduct K n h i ⟶ integralCurve (W) :=
  completeIdentityActionToCubicProduct K n h i ≫ leftSmoothFactorAddition (W)

/-- Its coefficient morphism is the original second input's base morphism. -/
@[reassoc] theorem completeIdentityActionTarget_structure :
    completeIdentityActionTarget K n h i ≫ integralCurveStructure (W) =
      pullback.snd (G).X.hom (π) ≫ (π) ≫ (S).toSpecΓ := by
  rw [completeIdentityActionTarget, Category.assoc, leftSmoothFactorAddition_structure,
    completeIdentityActionToCubicProduct_fst_assoc,
    completeIdentityActionParameter_structure, ← Category.assoc, pullback.condition,
    Category.assoc]

/-- The original zero marking paired with every point of the entire polygon. -/
def completeIdentityActionZeroGraph :
    exactVeroneseProj K n h ⟶ completeIdentityActionProduct K n h i :=
  pullback.lift ((π) ≫ completePointIdentityMarking K n h i) (𝟙 _) (by
    rw [Category.assoc, completePointOriginalBaseGroup_structure,
      completePointIdentityMarking_inclusion_assoc, completeBaseMarking_toBase,
      Category.comp_id, Category.id_comp])

/-- Acting by the original marking recovers the unchanged whole contraction. -/
@[reassoc] theorem completeIdentityActionZeroGraph_target :
    completeIdentityActionZeroGraph K n h i ≫ completeIdentityActionTarget K n h i =
      (g) := by
  have he : completeIdentityActionZeroGraph K n h i ≫
      completeIdentityActionToCubicProduct K n h i =
      (g) ≫ leftSmoothFactorZero (W) := by
    apply pullback.hom_ext
    · rw [Category.assoc, completeIdentityActionToCubicProduct_fst,
        ← Category.assoc, completeIdentityActionZeroGraph, pullback.lift_fst,
        Category.assoc, completePointIdentityMarking_toSmooth,
        Category.assoc, leftSmoothFactorZero_fst,
        completePointToIntegralCubic_over_assoc]
    · rw [Category.assoc, completeIdentityActionToCubicProduct_snd,
        ← Category.assoc, completeIdentityActionZeroGraph, pullback.lift_snd,
        Category.id_comp, Category.assoc, leftSmoothFactorZero_snd, Category.comp_id]
  rw [completeIdentityActionTarget, ← Category.assoc, he, Category.assoc,
    leftSmoothFactorAddition_left_identity, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimalStages
