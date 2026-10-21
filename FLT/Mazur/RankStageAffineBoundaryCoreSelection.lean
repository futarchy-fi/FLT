/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageAffineFullBoundaryTower
public import FLT.Mazur.RankStageGlobalBoundaryCoreCorrection
public import FLT.Mazur.RankStageOriginalBoundaryScalarObstruction

/-!
# Correcting the actual original-boundary towers on arbitrary cores

A full affine rank tower supplies one global boundary lift. Subtracting its
restriction from each independently chosen original-boundary tower gives an
ordinary compatible homogeneous correction on every whole core. The corrected
lifts agree on all overlaps, with no clopen assumption on those cores.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance affineSelectionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance affineSelectionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance affineSelectionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  [∀ k, IsAffine (rankThickening (Over.mk p) n k)]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageGlobalCoreRestriction rankStageInvariantTransition rankStageChosenBoundaryCoreTower

/-- Choose the full global boundary tower proved to exist by finite etale simultaneous lifting. -/
def rankStageAffineChosenBoundaryTower : rankStageCompatibleInvariants e n :=
  ⟨(exists_rankStage_affine_full_original_boundary_tower e n J hJ f hf t).choose,
    (exists_rankStage_affine_full_original_boundary_tower e n J hJ f hf t).choose_spec.1⟩

omit [IsAffine A] in
/-- Every chosen coefficient has exactly the prescribed full original boundary. -/
theorem rankStageAffineChosenBoundaryTower_boundary (k : ℕ) :
    (rankStageBoundaryIdeal (p := p) n k J).subschemeι.appTop
        ((rankStageAffineChosenBoundaryTower e n J hJ f hf t).val k).val =
      (rankStageFullOriginalBoundaryMap (p := p) n J k).appTop t.val :=
  (exists_rankStage_affine_full_original_boundary_tower e n J hJ f hf t).choose_spec.2 k

attribute [local irreducible] rankStageAffineChosenBoundaryTower

variable (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
local notation "v" => rankStageChosenBoundaryCoreTower e n a ha J hJ f hf t
local notation "w" => rankStageAffineChosenBoundaryTower e n J hJ f hf t

/-- A constructed full compatible correction for the actual chosen original-boundary lift. -/
def rankStageAffineBoundaryCorrection : rankStageCompatibleCoreInvariants e n a ha :=
  rankStageGlobalBoundaryCoreCorrection e n a ha v w

/-- The correction lies in the full original homogeneous boundary kernel at every order. -/
theorem rankStageAffineBoundaryCorrection_boundary (k : ℕ) :
    (rankStageCoreBoundaryIdeal e n a ha J k).subschemeι.appTop
      ((rankStageAffineBoundaryCorrection e n J hJ f hf t a ha).val k).val = 0 :=
  rankStageGlobalBoundaryCoreCorrection_boundary e n a ha J v w t.val
    (rankStageChosenBoundaryCoreTower_boundary e n a ha J hJ f hf t)
    (rankStageAffineChosenBoundaryTower_boundary e n J hJ f hf t) k

/-- Corrected towers are the restrictions of one full global tower, at every order. -/
theorem rankStageAffineBoundaryCorrection_corrects :
    v - rankStageAffineBoundaryCorrection e n J hJ f hf t a ha =
      rankStageCompatibleCoreRestriction e n a ha w :=
  rankStageGlobalBoundaryCoreCorrection_corrects e n a ha v w

variable (b : Γ(A, ⊤)) (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n)

/-- The actual full overlap obstruction is the coboundary of the constructed core corrections. -/
theorem rankStageAffineBoundaryCorrection_overlap (k : ℕ) :
    rankStageInvariantOverlapError e n a b ha hb k
        ((rankStageAffineBoundaryCorrection e n J hJ f hf t a ha).val k)
        ((rankStageAffineBoundaryCorrection e n J hJ f hf t b hb).val k) =
      rankStageInvariantOverlapError e n a b ha hb k ((v).val k)
        ((rankStageChosenBoundaryCoreTower e n b hb J hJ f hf t).val k) :=
  rankStageGlobalBoundaryCoreCorrection_overlap e n a ha b hb v
    (rankStageChosenBoundaryCoreTower e n b hb J hJ f hf t) w k

end FLT.Mazur.EquivalenceRelationOrderedFrames
