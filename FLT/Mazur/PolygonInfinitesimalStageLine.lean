/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealPullbackComparison
public import FLT.Mazur.PolygonInfinitesimalStageDivisor

/-!
# Positive boundary lines throughout the concrete infinitesimal system

The actual finite flat boundary ideals give locally free rank-one sheaves.
Every system transition has the canonical divisor-line pullback comparison.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type u) [CommRing R] (m n : ℕ) (h : 2 ≤ n)

/-- The positive line of the finite flat unit-one boundary on a concrete stage. -/
def boundaryLine : (family R m n h).left.Modules :=
  divisorLineBundle (boundaryIdeal R m n h) (boundaryIdeal_cartier R m n h).1

/-- Every concrete boundary line is locally free of rank one. -/
theorem boundaryLine_rankOne : LocallyFreeRankOne (boundaryLine R m n h) :=
  (boundaryIdeal_cartier R m n h).1.divisorLineBundle_locallyFreeRankOne

variable {a b : ℕ} (f : a ⟶ b)

/-- The actual ideal-module comparison is invertible on every system transition. -/
instance boundaryIdeal_systemMap_isIso :
    IsIso (idealModulePullbackHom (boundaryIdeal R b n h) ((stageSystem R n h).map f)) := by
  apply idealModulePullbackHom_isIso_of_cartier _ (boundaryIdeal_cartier R b n h).1
  rw [boundaryIdeal_systemMap]
  exact (boundaryIdeal_cartier R a n h).1

/-- Every transition compares the actual positive boundary lines. -/
def boundaryLineSystemIso :
    (pullback ((stageSystem R n h).map f)).obj (boundaryLine R b n h) ≅
      boundaryLine R a n h := by
  let _ := boundaryIdeal_systemMap_isIso R n h f
  exact divisorLinePullbackIsoOfEq (I := boundaryIdeal R b n h)
    (J := boundaryIdeal R a n h) ((stageSystem R n h).map f)
    (boundaryIdeal_cartier R b n h).1
    (boundaryIdeal_cartier R a n h).1 (boundaryIdeal_systemMap R n h f)

end FLT.Mazur.PolygonInfinitesimalStages
