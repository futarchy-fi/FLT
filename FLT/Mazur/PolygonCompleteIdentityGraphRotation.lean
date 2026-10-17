/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphRotatedContraction
public import FLT.Mazur.PolygonCompleteIdentitySmoothInputGraph

/-!
# Rotation on the unchanged complete graph

Schematic density of the original smooth graph gives a factorization through
its full closed image. Both original coordinates rotate, including at nodes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open GroupObjectPointTranslation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (b : ZMod n)
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "V" => completeIdentityActionSmoothOpen K n h
local notation "H" => completeIdentityActionGraphClosure K n h
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "j" => completeIdentityActionGraphInclusion K n h
local notation "u" => completeIdentityActionSmoothToGraph K n h
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "r" => completeIdentityActionInputRotation K n h b
local notation "t" => completeRotation K n h b

/-- Rotation gives a morphism from the entire graph to its original ambient lifting space. -/
def completeIdentityGraphRotatedAmbient : (H) ⟶ completeIdentityActionLiftSpace K n h :=
  pullback.lift ((p) ≫ (r)) ((l) ≫ (t))
    (by simpa only [Category.assoc] using
      (completeIdentityActionGraphLift_rotatedContraction K n h b).symm)

/-- Rotating the smooth coordinates still gives a point of the original smooth graph. -/
def completeIdentitySmoothGraphRotation : (V).toScheme ⟶ (H) :=
  completeIdentityActionSmoothCoordinates K n h ≫
    (𝟙 (G).X ⊗ₘ translation (completeOriginalSmoothCyclicPoint K n h b)).left ≫
      completeIdentitySmoothInputToGraph K n h

/-- The smooth rotation has the prescribed whole-input coordinate. -/
@[reassoc] theorem completeIdentitySmoothGraphRotation_source :
    completeIdentitySmoothGraphRotation K n h b ≫ (p) = (V).ι ≫ (r) := by
  rw [completeIdentitySmoothGraphRotation, Category.assoc, Category.assoc,
    completeIdentitySmoothInputToGraph_source, completeIdentitySmoothActionInput_rotation,
    completeIdentityActionSmoothCoordinates_input_assoc]

/-- Its target is the original polygon rotation of the original smooth action. -/
@[reassoc] theorem completeIdentitySmoothGraphRotation_target :
    completeIdentitySmoothGraphRotation K n h b ≫ (l) =
      completeIdentityActionSmoothLift K n h ≫ (t) := by
  rw [completeIdentitySmoothGraphRotation, Category.assoc, Category.assoc,
    completeIdentitySmoothInputToGraph_target,
    completeIdentitySmoothAction_rotation_inclusion]
  rfl

/-- The rotated ambient map factors through the original graph on its dense smooth open. -/
@[reassoc] theorem completeIdentitySmoothGraphRotation_ambient :
    completeIdentitySmoothGraphRotation K n h b ≫ (j) =
      (u) ≫ completeIdentityGraphRotatedAmbient K n h b := by
  apply pullback.hom_ext
  · change completeIdentitySmoothGraphRotation K n h b ≫ (p) = _
    rw [completeIdentitySmoothGraphRotation_source, Category.assoc,
      completeIdentityGraphRotatedAmbient, pullback.lift_fst,
      completeIdentityActionSmoothToGraph_projection_assoc]
  · change completeIdentitySmoothGraphRotation K n h b ≫ (l) = _
    rw [completeIdentitySmoothGraphRotation_target, Category.assoc,
      completeIdentityGraphRotatedAmbient, pullback.lift_snd,
      completeIdentityActionSmoothToGraph_lift_assoc]

/-- Density detects containment of the full graph ideal, retaining nilpotents. -/
theorem completeIdentityGraphRotatedAmbient_kernel :
    (j).ker ≤ (completeIdentityGraphRotatedAmbient K n h b).ker := by
  have he := (completeIdentitySmoothGraphRotation K n h b).le_ker_comp (j)
  rw [completeIdentitySmoothGraphRotation_ambient, Scheme.Hom.ker_comp,
    Scheme.Hom.ker_eq_bot (u), Scheme.IdealSheafData.map_bot] at he
  exact he

/-- The original rotations act on the unchanged schematic graph closure. -/
def completeIdentityGraphRotation : (H) ⟶ (H) :=
  IsClosedImmersion.lift (j) (completeIdentityGraphRotatedAmbient K n h b)
    (completeIdentityGraphRotatedAmbient_kernel K n h b)

/-- Closed factorization retains the original ambient morphism. -/
@[reassoc] theorem completeIdentityGraphRotation_inclusion :
    completeIdentityGraphRotation K n h b ≫ (j) =
      completeIdentityGraphRotatedAmbient K n h b := IsClosedImmersion.lift_fac _ _ _

/-- Rotation on the entire graph retains the original whole-input rotation. -/
@[reassoc] theorem completeIdentityGraphRotation_source :
    completeIdentityGraphRotation K n h b ≫ (p) = (p) ≫ (r) := by
  rw [completeIdentityActionGraphProjection, completeIdentityGraphRotation_inclusion_assoc,
    completeIdentityGraphRotatedAmbient, pullback.lift_fst]
  rfl

/-- Rotation on the entire graph retains the original whole-family target rotation. -/
@[reassoc] theorem completeIdentityGraphRotation_target :
    completeIdentityGraphRotation K n h b ≫ (l) = (l) ≫ (t) := by
  rw [completeIdentityActionGraphLift, completeIdentityGraphRotation_inclusion_assoc,
    completeIdentityGraphRotatedAmbient, pullback.lift_snd]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
