/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineTrivializationCoordinates
public import FLT.Mazur.LinearCoordinateRatio
public import FLT.Mazur.ModuleSheafUnitCocycle

/-!
# Transition cocycles of genuine line trivializations

Local linear coordinates give units on every common subopen. Naturality
and the cocycle equations follow from the actual section isomorphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.Approximation

namespace FLT.Mazur.FCurve

universe u

variable {X : Scheme.{u}} {L : X.Modules} {ι : Type u} {U : ι → X.Opens}
  (e : ∀ i, L.restrict (U i).ι ≅ structureModule (U i).toScheme)

/-- The actual unit ratio between two local trivializations. -/
def lineTrivializationUnit (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    Γ(X, V)ˣ :=
  linearCoordinateRatio (lineTrivializationCoordinates (e i) hi)
    (lineTrivializationCoordinates (e j) hj)

/-- The genuine coordinate ratios commute with restriction. -/
theorem lineTrivializationUnit_natural (i j : ι) {V W : X.Opens}
    (h : W ≤ V) (hi : V ≤ U i) (hj : V ≤ U j) :
    ModuleSheafUnitCocycle.res h (lineTrivializationUnit e i j V hi hj : Γ(X, V)) =
      (lineTrivializationUnit e i j W (h.trans hi) (h.trans hj) : Γ(X, W)) := by
  change X.presheaf.map (homOfLE h).op
      (lineTrivializationCoordinates (e i) hi
        ((lineTrivializationCoordinates (e j) hj).symm 1)) = _
  rw [← lineTrivializationCoordinates_restrict,
    ← lineTrivializationCoordinates_symm_restrict]
  simp only [map_one]
  rfl

/-- An ambient unit cocycle constructed from the chosen sheaf trivializations. -/
def lineTrivializationCocycle : ModuleSheafUnitCocycle.Cocycle U where
  unit := lineTrivializationUnit e
  natural := lineTrivializationUnit_natural e
  refl i _ h := linearCoordinateRatio_self (lineTrivializationCoordinates (e i) h)
  cocycle i j k _ hi hj hk := linearCoordinateRatio_mul
    (lineTrivializationCoordinates (e i) hi) (lineTrivializationCoordinates (e j) hj)
    (lineTrivializationCoordinates (e k) hk)

/-- The transition functions compare the actual coordinates of every section. -/
theorem lineTrivializationCocycle_coordinates (i j : ι) (V : X.Opens)
    (hi : V ≤ U i) (hj : V ≤ U j) (s : Γ(L, V)) :
    lineTrivializationCoordinates (e i) hi s =
      ((lineTrivializationCocycle e).unit i j V hi hj : Γ(X, V)) *
        lineTrivializationCoordinates (e j) hj s :=
  linearCoordinateRatio_smul _ _ s

end FLT.Mazur.FCurve
