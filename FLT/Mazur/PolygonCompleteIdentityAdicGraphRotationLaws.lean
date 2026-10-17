/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicGraphRotation
public import FLT.Mazur.PolygonCompleteIdentityAdicGraphCoherence

/-!
# Cyclic laws and restriction compatibility on the actual adic graph

Every literal adic graph inherits automorphisms from the complete graph.
They commute with adjacent restriction of the original thickenings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "j" => completeIdentityActionGraphStageInclusion K n h m
local notation "R" => completeIdentityAdicGraphRotation K n h m

/-- The zero rotation fixes the literal adic graph. -/
theorem completeIdentityAdicGraphRotation_zero : R 0 = 𝟙 _ := by
  apply (cancel_mono (j)).mp
  rw [completeIdentityAdicGraphRotation_complete, completeIdentityGraphRotation_zero,
    Category.comp_id, Category.id_comp]

/-- The literal adic graph retains the cyclic addition law. -/
theorem completeIdentityAdicGraphRotation_add (b c : ZMod n) : R (b + c) = R b ≫ R c := by
  apply (cancel_mono (j)).mp
  rw [completeIdentityAdicGraphRotation_complete, completeIdentityGraphRotation_add,
    Category.assoc, completeIdentityAdicGraphRotation_complete,
    completeIdentityAdicGraphRotation_complete_assoc]

/-- Each rotation is an automorphism of the unchanged adic graph, with its full ideal. -/
def completeIdentityAdicGraphRotationIso (b : ZMod n) :
    completeIdentityActionGraphStage K n h m ≅ completeIdentityActionGraphStage K n h m where
  hom := R b
  inv := R (-b)
  hom_inv_id := by rw [← completeIdentityAdicGraphRotation_add, add_neg_cancel,
    completeIdentityAdicGraphRotation_zero]
  inv_hom_id := by rw [← completeIdentityAdicGraphRotation_add, neg_add_cancel,
    completeIdentityAdicGraphRotation_zero]

instance completeIdentityAdicGraphRotation_isIso (b : ZMod n) : IsIso (R b) :=
  (completeIdentityAdicGraphRotationIso K n h m b).isIso_hom

/-- The entire compatible tower carries the same original cyclic action. -/
@[reassoc] theorem completeIdentityAdicGraphRotation_restriction (b : ZMod n) :
    R b ≫ completeIdentityAdicGraphRestriction K n h m =
      completeIdentityAdicGraphRestriction K n h m ≫
        completeIdentityAdicGraphRotation K n h (m + 1) b := by
  apply (cancel_mono (completeIdentityActionGraphStageInclusion K n h (m + 1))).mp
  rw [Category.assoc, completeIdentityAdicGraphRestriction_complete,
    completeIdentityAdicGraphRotation_complete, Category.assoc,
    completeIdentityAdicGraphRotation_complete, completeIdentityAdicGraphRestriction_complete_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
