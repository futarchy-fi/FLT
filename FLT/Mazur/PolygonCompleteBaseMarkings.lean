/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNeighborhoodStageReconstruction
public import FLT.Mazur.PolygonMarkingAffineNeighborhood

/-!
# Actual markings over the complete power-series base

The original compatible finite-order markings lie in common affine charts.
Reconstruction in those charts gives sections over the complete base with
exactly the original restrictions at every order.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- A common affine neighborhood of every order of the specified original marking. -/
def originalMarkingAffineOpen (i : Fin n) : (exactVeroneseProj K n h).Opens :=
  (originalMarking_exists_affine K n h i).choose

/-- The selected neighborhood is affine. -/
theorem originalMarkingAffineOpen_isAffine (i : Fin n) :
    IsAffineOpen (originalMarkingAffineOpen K n h i) :=
  (originalMarking_exists_affine K n h i).choose_spec.1

/-- All original stages of the marking factor through the selected affine neighborhood. -/
theorem originalMarkingAffineOpen_contains (i : Fin n) (m : ℕ) :
    Set.range ((originalMarkingCompatibleProj K n h i).app m) ⊆
      (originalMarkingAffineOpen K n h i : Set (exactVeroneseProj K n h)) :=
  (originalMarking_exists_affine K n h i).choose_spec.2 m

/-- The actual section reconstructed from the original polygon marking at every order. -/
def completeBaseMarking (i : Fin n) :
    Spec (.of (PowerSeries K)) ⟶ exactVeroneseProj K n h :=
  pointFromAffineStages K (originalMarkingCompatibleProj K n h i)
    (originalMarkingAffineOpen K n h i) (originalMarkingAffineOpen_isAffine K n h i)
    (originalMarkingAffineOpen_contains K n h i)

/-- Every original finite-order marking is the actual restriction of the complete marking. -/
@[reassoc] theorem baseToSeries_completeBaseMarking (i : Fin n) (m : ℕ) :
    baseToSeries K m ≫ completeBaseMarking K n h i =
      marking K m n h i ≫ originalStageToCompatibleProj K n h m :=
  baseToSeries_pointFromAffineStages K _ _ _ _ m

/-- The reconstructed complete-base marking is a section of the actual structural morphism. -/
@[reassoc] theorem completeBaseMarking_toBase (i : Fin n) :
    completeBaseMarking K n h i ≫ exactVeroneseProjToBase K n h = 𝟙 _ :=
  pointFromAffineStages_toBase K _ _ _ _ _
    (originalMarkingCompatibleProj_toBase K n h i)

end FLT.Mazur.PolygonInfinitesimalStages
