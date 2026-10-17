/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityWholeAction
public import FLT.Mazur.PolygonCompleteIdentitySmoothInputGraph

/-!
# The whole original action retains smooth multiplication and rotations

Schematic density of the original smooth input detects equalities on the full
input. Consequently the constructed whole action commutes with every original
rotation, including on the singular inputs.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open GroupObjectPointTranslation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => completeIdentityActionProduct K n h 0
local notation "π" => exactVeroneseProjToBase K n h
local notation "V" => completeIdentityActionSmoothOpen K n h
local notation "u" => completeIdentitySmoothActionInput K n h
local notation "a" => completeIdentityWholeAction K n h

/-- The global action restricts to the constructed action on the full smooth-input open. -/
@[reassoc] theorem completeIdentityWholeAction_smooth :
    (V).ι ≫ (a) = completeIdentityActionSmoothLift K n h :=
  completeIdentityWholeAction_chart K n h none

/-- The global action agrees with actual original smooth multiplication on smooth pairs. -/
@[reassoc] theorem completeIdentityWholeAction_smoothInput :
    (u) ≫ (a) = (completeIdentitySmoothAction K n h).left ≫ (π).smoothLocus.ι := by
  rw [← completeIdentitySmoothInputToOpen_input K n h, Category.assoc,
    completeIdentityWholeAction_smooth, completeIdentitySmoothInputToOpen_lift]

/-- Equality on the actual smooth inputs detects maps on the full original input scheme. -/
theorem completeIdentityWholeInput_ext (f g : (P) ⟶ exactVeroneseProj K n h)
    (hb : f ≫ (π) = g ≫ (π)) (he : (u) ≫ f = (u) ≫ g) : f = g := by
  let _ := exactVeroneseProjToBase_isProper K n h
  apply Chow.schematicallyDense_ext (π) hb (V).ι
  rw [← completeIdentityActionSmoothCoordinates_input K n h, Category.assoc, he,
    Category.assoc]

/-- The entire original action commutes with rotation of its whole second input. -/
@[reassoc] theorem completeIdentityWholeAction_rotation (b : ZMod n) :
    completeIdentityActionInputRotation K n h b ≫ (a) =
      (a) ≫ completeRotation K n h b := by
  apply completeIdentityWholeInput_ext K n h
  · rw [Category.assoc, completeIdentityWholeAction_structure,
      completeIdentityActionInputRotation_structure, Category.assoc,
      completeRotation_toBase, completeIdentityWholeAction_structure]
  · rw [← completeIdentitySmoothActionInput_rotation_assoc,
      completeIdentityWholeAction_smoothInput, completeIdentityWholeAction_smoothInput_assoc,
      completeIdentitySmoothAction_rotation_inclusion]

/-- The original zero marking acts as the identity on the entire original polygon. -/
@[reassoc] theorem completeIdentityWholeAction_zero :
    completeIdentityActionZeroGraph K n h 0 ≫ (a) = 𝟙 _ := by
  let _ := exactVeroneseProjToBase_flat K n h
  apply completeFlat_contraction_ext K n h 0 (π)
  · rw [Category.assoc, completeIdentityWholeAction_structure,
      completeIdentityActionZeroGraph, pullback.lift_snd_assoc, Category.id_comp]
  · exact Category.id_comp _
  · rw [Category.assoc, completeIdentityWholeAction_cubic,
      completeIdentityActionZeroGraph_target, Category.id_comp]

end FLT.Mazur.PolygonInfinitesimalStages
