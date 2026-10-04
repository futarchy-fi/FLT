/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveSectionExtension
public import FLT.Mazur.AmpleAffinePullback
public import FLT.Mazur.CocycleGlobalSectionCoordinate

/-!
# Coordinate sections of the hyperplane bundle

The homogeneous coordinates are actual global sections of the cocycle-defined
hyperplane sheaf. Their coefficients on chart j are X_i/X_j.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open FLT.Mazur.FCurve FLT.Mazur.FCurve.ModuleSheafUnitCocycle
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (ι : Type u)

/-- A homogeneous coordinate, assembled from its ratios on every standard chart. -/
def coordinateGlobalSection (i : ι) : (twistCocycle R ι 1).sections ⊤ :=
  ⟨fun j ↦ res inf_le_right (chartCoordinateSection R ι j i), by
    intro j k W hj hk
    have h := congrArg (res (le_inf (hj.trans inf_le_right) (hk.trans inf_le_right)))
      (chartCoordinateSection_cocycle R ι j k i)
    change res hj (res inf_le_right (chartCoordinateSection R ι j i)) =
      res (le_inf (hj.trans inf_le_right) (hk.trans inf_le_right))
        (twistTransition R ι 1 j k : Γ(space R ι, chart R ι j ⊓ chart R ι k)) *
      res hk (res inf_le_right (chartCoordinateSection R ι k i))
    simpa only [map_mul, res_res] using h⟩


/-- Restricting the coordinate section and evaluating gives its chart ratio. -/
lemma coordinateGlobalSection_evaluate (i j : ι) (V : (space R ι).Opens)
    (hV : V ≤ chart R ι j) :
    (twistCocycle R ι 1).evaluate j hV
      ((twistCocycle R ι 1).restrict le_top (coordinateGlobalSection R ι i)) =
      res hV (chartCoordinateSection R ι j i) := by
  change res _ (res _ (res _ (chartCoordinateSection R ι j i))) = _
  simp only [res_res]

/-- The standard trivialization reads off the coordinate ratio on global chart sections. -/
lemma coordinateGlobalSection_chart (i j : ι) :
    ((twistCocycle R ι 1).onOpenIso j (chart R ι j) le_rfl).hom.app ⊤
      ((twistCocycle R ι 1).restrict le_top (coordinateGlobalSection R ι i)) =
      (chart R ι j).topIso.inv (chartCoordinateSection R ι j i) := by
  exact (Cocycle.onOpenIso_globalSection_coordinate (twistCocycle R ι 1) j _ le_rfl
    (coordinateGlobalSection R ι i)).trans
      (congrArg ((chart R ι j).topIso.inv)
        ((coordinateGlobalSection_evaluate R ι i j _ le_rfl).trans (res_self _ _)))

end FLT.Mazur.ProjectiveSpace
