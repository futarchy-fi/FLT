/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedSubframe

/-!
# Normalize an arbitrary original frame at any selected endpoint

An arbitrary test frame need not already have its first endpoint among its
second endpoints. Rebasing at a selected coordinate constructs a normalized
frame while retaining every original second endpoint on the entire test.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A T : Scheme} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  (I : Type) [Fintype I] (o : I) {b : T ⟶ A}

local instance normalizeOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
variable (t : Over.mk b ⟶ distinctScheme (Over.mk p) I)

/-- Move the whole original frame to the second endpoint of its selected coordinate. -/
def normalizationFrame :
    Over.mk ((t ≫ distinctCoordinate (Over.mk p) I o).left ≫ q) ⟶
      distinctScheme (Over.mk p) I :=
  rebaseFrame e I (t ≫ distinctCoordinate (Over.mk p) I o).left
    (frameCast I (t ≫ distinctCoordinate (Over.mk p) I o).w.symm t)

/-- Every second endpoint survives this rebasing as an actual scheme morphism. -/
@[reassoc] theorem normalizationFrame_second (i : I) :
    (normalizationFrame e I o t ≫ distinctCoordinate (Over.mk p) I i).left ≫ q =
      (t ≫ distinctCoordinate (Over.mk p) I i).left ≫ q :=
  rebaseFrame_second e I _ _ i

/-- The normalized source test constructed from an arbitrary original frame. -/
def normalizeFrame : T ⟶ source p q I o :=
  lift p q I o (normalizationFrame e I o t) (normalizationFrame_second e I o t o).symm

/-- Normalization retains every independent second endpoint, including on nilpotent tests. -/
@[reassoc] theorem normalizeFrame_second (i : I) :
    normalizeFrame e I o t ≫ coordinate p q I o i ≫ q =
      (t ≫ distinctCoordinate (Over.mk p) I i).left ≫ q := by
  rw [← Category.assoc, normalizeFrame, lift_coordinate, normalizationFrame_second]

/-- Normalization puts the first endpoint at the selected original second endpoint. -/
@[reassoc] theorem normalizeFrame_first :
    normalizeFrame e I o t ≫ first p q I o =
      (t ≫ distinctCoordinate (Over.mk p) I o).left ≫ q :=
  lift_first p q I o _ _

/-- Selecting a subframe after normalization keeps the original selected second endpoints. -/
@[reassoc] theorem normalizeFrame_subframe_second {J : Type} [Fintype J]
    (o' : J) (ι : J ↪ I) (j : J) :
    normalizeFrame e I o t ≫ subframeMap e o o' ι ≫ coordinate p q J o' j ≫ q =
      (t ≫ distinctCoordinate (Over.mk p) I (ι j)).left ≫ q := by
  rw [subframeMap_second, normalizeFrame_second]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
