/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticPointReconstruction
public import FLT.Mazur.PolygonArithmeticMarkingNeighborhood

/-!
# Actual markings over the complete power-series base

The original compatible finite-order markings lie in common affine charts.
Reconstruction in those charts gives sections over the complete base with
exactly the original restrictions at every order.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- A common affine neighborhood of every order of the specified original marking. -/
def originalMarkingAffineOpen (i : Fin n) : (exactVeroneseProj A π n h hne hgen).Opens :=
  (originalMarking_exists_affine A π hgen hne n h i).choose

/-- The selected neighborhood is affine. -/
theorem originalMarkingAffineOpen_isAffine (i : Fin n) :
    IsAffineOpen (originalMarkingAffineOpen A π hne hgen n h i) :=
  (originalMarking_exists_affine A π hgen hne n h i).choose_spec.1

/-- All original stages of the marking factor through the selected affine neighborhood. -/
theorem originalMarkingAffineOpen_contains (i : Fin n) (m : ℕ) :
    Set.range ((originalMarkingCompatibleProj A π hne hgen n h i).app m) ⊆
      (originalMarkingAffineOpen A π hne hgen n h i : Set (exactVeroneseProj A π n h hne hgen)) :=
  (originalMarking_exists_affine A π hgen hne n h i).choose_spec.2 m

variable [IsAdicComplete (ideal A π) A]

/-- The actual section reconstructed from the original polygon marking at every order. -/
def completeBaseMarking (i : Fin n) :
    Spec (.of A) ⟶ exactVeroneseProj A π n h hne hgen :=
  pointFromAffineStages A π (originalMarkingCompatibleProj A π hne hgen n h i)
    (originalMarkingAffineOpen A π hne hgen n h i) (originalMarkingAffineOpen_isAffine A π hne
    hgen n h i)
    (originalMarkingAffineOpen_contains A π hne hgen n h i)

/-- Every original finite-order marking is the actual restriction of the complete marking. -/
@[reassoc] theorem baseToIntegral_completeBaseMarking (i : Fin n) (m : ℕ) :
    baseToIntegral A π m ≫ completeBaseMarking A π hne hgen n h i =
      marking A π m n h i ≫ originalStageToCompatibleProj A π hne hgen n h m :=
  baseToIntegral_pointFromAffineStages A π _ _ _ _ m

/-- The reconstructed complete-base marking is a section of the actual structural morphism. -/
@[reassoc] theorem completeBaseMarking_toBase (i : Fin n) :
    completeBaseMarking A π hne hgen n h i ≫ exactVeroneseProjToBase A π n h hne hgen = 𝟙 _ :=
  pointFromAffineStages_toBase A π _ _ _ _ _
    (originalMarkingCompatibleProj_toBase A π hne hgen n h i)

end FLT.Mazur.PolygonArithmeticStages
