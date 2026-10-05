/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntersectionUnitCocycle

/-!
# Recovering genuine transitions from the intersection construction

For the actual intersections of an open family, the singleton construction
recovers the original cocycle units on every common subopen. The indexed
units also agree with the finite coordinate units used in coefficient descent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.Approximation

universe u

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (g : Cocycle U)

/-- The original ambient unit on a finite intersection. -/
def originalIntersectionUnit (s : NonemptyChartSet ι) (k : IntersectionPair s) :
    Γ(X, finiteIntersectionOpen U s)ˣ :=
  g.unit k.1.val k.2.val (finiteIntersectionOpen U s)
    (finiteIntersectionOpen_le_chart U s k.1) (finiteIntersectionOpen_le_chart U s k.2)

/-- Original intersection units commute with adding chart labels. -/
theorem originalIntersectionUnit_naturality {s t : NonemptyChartSet ι}
    (h : s ≤ t) (k : IntersectionPair s) :
    res (finiteIntersectionOpen_antitone U h)
        (originalIntersectionUnit U g s k : Γ(X, finiteIntersectionOpen U s)) =
      (originalIntersectionUnit U g t (intersectionPairMap (homOfLE h) k) :
        Γ(X, finiteIntersectionOpen U t)) :=
  g.natural _ _ _ _ _

/-- Original intersection units satisfy the triple multiplication equations. -/
theorem originalIntersectionUnit_mul (s : NonemptyChartSet ι) (k : IntersectionTriple s) :
    originalIntersectionUnit U g s (k.1, k.2.1) *
      originalIntersectionUnit U g s (k.2.1, k.2.2) =
        originalIntersectionUnit U g s (k.1, k.2.2) :=
  g.cocycle _ _ _ _ _ _ _

/-- The intersection construction applied to the original transitions. -/
def originalIntersectionCocycle :
    Cocycle (fun i ↦ finiteIntersectionOpen U (singletonChartSet i)) :=
  intersectionUnitsCocycle (finiteIntersectionOpen U) (finiteIntersectionOpen_antitone U)
    (finiteIntersectionOpen_union U) (originalIntersectionUnit U g)
    (originalIntersectionUnit_naturality U g) (originalIntersectionUnit_mul U g)

/-- Singleton reconstruction agrees with the original unit on every common subopen. -/
theorem originalIntersectionCocycle_unit (i j : ι) (V : X.Opens)
    (hi : V ≤ finiteIntersectionOpen U (singletonChartSet i))
    (hj : V ≤ finiteIntersectionOpen U (singletonChartSet j)) :
    (originalIntersectionCocycle U g).unit i j V hi hj =
      g.unit i j V (by simpa using hi) (by simpa using hj) := by
  apply Units.ext
  change res _ (g.unit i j (finiteIntersectionOpen U (pairChartSet i j)) _ _ :
    Γ(X, finiteIntersectionOpen U (pairChartSet i j))) = _
  exact g.natural _ _ _ _ _

/-- The finite coordinate units are exactly the coordinates of these ambient units. -/
theorem originalIntersectionUnit_coordinates {A : Type u} [CommRing A]
    (p : X ⟶ Spec (.of A)) (s : NonemptyChartSet ι) (k : IntersectionPair s) :
    Units.map (finiteIntersectionSectionEquiv U p s).toMonoidHom
        (originalIntersectionUnit U g s k) = finiteIntersectionCocycleUnit U p g s k := rfl

end FLT.Mazur.Approximation
