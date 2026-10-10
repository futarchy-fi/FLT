/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOverlapProjectionRecovery

/-!
# Recovering chart transitions from ambient projections

A projection equation on an overlap determines the transition between
recovered chart modules. The calculation is abstract in the coordinate
rings so that concrete descended sheaves need not be expanded.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafChartOverlapRecovery

open ModuleSheafOverlapImageTransition

/-- An ambient projection equation recovers the original coefficient transition. -/
lemma recovery_overlap {X Y Z O : Scheme.{u}}
    (i : Y ⟶ X) (j : Z ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (p : O ⟶ Y) (q : O ⟶ Z) (r : O ⟶ X) (hi : p ≫ i = r) (hj : q ≫ j = r)
    (G : X.Modules) (M : Y.Modules) (N : Z.Modules)
    (a : G ⟶ (pushforward i).obj M) (b : G ⟶ (pushforward j).obj N)
    (e : (pullback p).obj M ≅ (pullback q).obj N)
    (u : (pullback r).obj G ⟶ (pullback p).obj M)
    (v : (pullback r).obj G ⟶ (pullback q).obj N)
    (hu : u = (pullback r).map a ≫ (coordinateIso p i r hi M).hom)
    (hv : v = (pullback r).map b ≫ (coordinateIso q j r hj N).hom)
    (h : (pullback r).map a ≫ (ambientIso i j p q r hi hj e).hom =
      (pullback r).map b) : u ≫ e.hom = v := by
  rw [hu, hv, Category.assoc, ← ambientIso_coordinate i j p q r hi hj e,
    ← Category.assoc, h]

end FLT.Mazur.ModuleSheafChartOverlapRecovery
