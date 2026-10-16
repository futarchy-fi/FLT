/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionInputRotation
public import FLT.Mazur.PolygonCompleteIdentityActionGraphCompatibility

/-!
# Rotated contraction equations on the unchanged original graph

The smooth action commutes with rotation. Schematic density extends this
identity to the full original graph closure before any adic specialization.
No graph ideal is replaced by a reduction or a branch image.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart GroupObjectPointTranslation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
  FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
attribute [local instance] exactVeroneseProjToBase_lfp completeSmoothGrpObj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (b : ZMod n)
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "π" => exactVeroneseProjToBase K n h
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "V" => completeIdentityActionSmoothOpen K n h
local notation "r" => completeIdentityActionInputRotation K n h b
local notation "t" => completeRotation K n h b
local notation "c" => completeIdentityActionSmoothCoordinates K n h

/-- The full smooth-input lift retains the rotated original contraction equation. -/
@[reassoc] theorem completeIdentityActionSmoothLift_rotatedContraction :
    completeIdentityActionSmoothLift K n h ≫ (t) ≫ (g) = (V).ι ≫ (r) ≫ (a) := by
  rw [completeIdentityActionSmoothLift]
  simp only [Category.assoc]
  rw [← completeIdentitySmoothAction_rotation_inclusion_assoc K n h b,
    completeIdentitySmoothAction_contraction,
    completeIdentitySmoothActionInput_rotation_assoc,
    completeIdentityActionSmoothCoordinates_input_assoc]

local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "s" => completeIdentityActionSecond K n h
local notation "u" => completeIdentityActionSmoothToGraph K n h
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "W" => completePointWeierstrassCurve K n h (0 : Fin n)

/-- Every cyclically rotated contraction equation holds on the entire original graph. -/
@[reassoc] theorem completeIdentityActionGraphLift_rotatedContraction :
    (l) ≫ (t) ≫ (g) = (p) ≫ (r) ≫ (a) := by
  let v := integralCurveStructure (W) ≫ inv (S).toSpecΓ
  let _ : IsSeparated v := by dsimp only [v]; infer_instance
  refine Chow.schematicallyDense_ext v ?_ (u) ?_
  · apply (cancel_mono (S).toSpecΓ).mp
    simp only [v, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      completePointToIntegralCubic_over, completeRotation_toBase_assoc,
      completeIdentityActionGraphLift_structure_assoc, completeIdentityActionTarget_structure,
      completeIdentityActionInputRotation_structure_assoc]
  · simp only [completeIdentityActionSmoothToGraph_lift_assoc,
      completeIdentityActionSmoothToGraph_projection_assoc,
      completeIdentityActionSmoothLift_rotatedContraction]

end FLT.Mazur.PolygonInfinitesimalStages
