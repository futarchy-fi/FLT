/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationJointChartBoundaryCover

/-!
# Projections from the entire mixed chart relation

Common-frame comparisons commute with both actual chart projections and the
full closed inclusion. These identities are on schemes, including nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
local notation "M" => mixedChartOpen o o' U V

/-- First projection from the full mixed chart relation. -/
def mixedChartFirst : (M).toScheme ⟶ U.toScheme :=
  (fst p q I J o o').resLE U _ inf_le_left

/-- Second projection from the full mixed chart relation. -/
def mixedChartSecond : (M).toScheme ⟶ V.toScheme :=
  (snd p q I J o o').resLE V _ inf_le_right

/-- The common-frame first map factors through the entire mixed relation. -/
@[reassoc] theorem jointChartMap_first (c : JointIndex I J) :
    jointChartMap e o o' U V c ≫ mixedChartFirst o o' U V =
      jointChartFirst e o o' c.2.val.1 c.2.val.2 U V := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, mixedChartFirst, Scheme.Hom.resLE_comp_ι,
    jointChartMap_inclusion_assoc, jointMap, jointGraph_fst, jointChartFirst_inclusion]

/-- The common-frame second map factors through the entire mixed relation. -/
@[reassoc] theorem jointChartMap_second (c : JointIndex I J) :
    jointChartMap e o o' U V c ≫ mixedChartSecond o o' U V =
      jointChartSecond e o o' c.2.val.1 c.2.val.2 U V := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, mixedChartSecond, Scheme.Hom.resLE_comp_ι,
    jointChartMap_inclusion_assoc, jointMap, jointGraph_snd, jointChartSecond_inclusion]

variable (i : B ⟶ A)
local notation "j" => jointBoundaryTargetInclusion (p := p) (q := q) o o' i

/-- The exact boundary inclusion restricted to the entire mixed chart relation. -/
def mixedChartBoundaryInclusion :
    (mixedChartBoundaryOpen o o' U V i).toScheme ⟶ (M).toScheme := j ∣_ M

/-- Common-chart boundary maps commute with the actual mixed boundary restriction. -/
@[reassoc] theorem jointChartBoundaryMap_ambient (c : JointIndex I J) :
    jointChartBoundaryMap e o o' U V i c ≫ mixedChartBoundaryInclusion o o' U V i =
      (InvariantBoundary.inclusion (Fin c.1.val) (c.2.val.1 o) i ∣_
        jointChartOpen e o o' c.2.val.1 c.2.val.2 U V) ≫ jointChartMap e o o' U V c := by
  apply (cancel_mono (M).ι).mp
  have h := jointChartBoundaryMap_inclusion_assoc e o o' U V i c j
  dsimp only [mixedChartBoundaryOpen] at h
  simp only [Category.assoc, mixedChartBoundaryInclusion, morphismRestrict_ι,
    h, jointBoundaryMap_inclusion, jointChartMap_inclusion, morphismRestrict_ι_assoc]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
