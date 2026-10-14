/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstOrderFactor

/-!
# Sealed original divisor line and first-order sections

These wrappers retain the original line and sections by exact equalities, while
preventing concrete frame consumers from expanding the complete-family construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor completeBaseMarking Scheme.Hom.ker

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "s" => completeBaseMarking K n h i
/-- The original marking is an effective Cartier divisor on the complete family. -/
theorem completePointFirstOrderCartier : EffectiveCartier (Scheme.Hom.ker (s)) :=
  (completeBaseMarking_relativeCartier K n h i).1

local notation "hI" => completePointFirstOrderCartier K n h i

/-- The original Cartier line, sealed for scalar-coordinate consumers. -/
irreducible_def completePointFirstOrderLine : (exactVeroneseProj K n h).Modules :=
  divisorLineBundle (Scheme.Hom.ker (s)) hI

local notation "L" => completePointFirstOrderLine K n h i

/-- The sealed line is the original effective Cartier line and is locally free of rank one. -/
theorem completePointFirstOrderLine_locallyFree : LocallyFreeRankOne (L) := by
  rw [completePointFirstOrderLine_def]
  exact (hI).divisorLineBundle_locallyFreeRankOne

end FLT.Mazur.PolygonInfinitesimalStages
