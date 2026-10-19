/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Base maps of morphisms between relative gluings

Compatibility of concrete chart maps with their base projections descends
to the map of colimits, without expanding a geometric gluing construction.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {S : Scheme.{u}} (U : S.OpenCover) [SmallCategory U.I₀]
  [U.LocallyDirected] [Small.{u} U.I₀] [Quiver.IsThin U.I₀]
  (d e : U.RelativeGluingData) (s : d.functor ⟶ e.functor)

/-- A map of relative gluings preserves the base when all its chart maps do. -/
theorem relativeGluing_colimMap_toBase
    (h : ∀ i, s.app i ≫ e.natTrans.app i = d.natTrans.app i) :
    colimMap s ≫ e.toBase = d.toBase := by
  apply colimit.hom_ext
  intro i
  rw [ι_colimMap_assoc, e.ι_toBase, ← Category.assoc, h, d.ι_toBase]

end FLT.Mazur
