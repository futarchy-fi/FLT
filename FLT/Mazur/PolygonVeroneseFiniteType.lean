/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseBoundedGenerators
public import FLT.Mazur.PolygonVeroneseClosedLifts
public import FLT.Mazur.PolygonVeroneseClosedGeneration

/-!
# Finite type of the actual compatible Veronese algebra

Finite compatible generators in bounded degrees lift every closed section
by the proved multiplication recurrence. Degreewise Nakayama then proves
that they generate the entire original compatible Veronese algebra over
the power-series base, with no closed-generation hypothesis.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family boundarySeriesScalars
attribute [local irreducible] Algebra.adjoin

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original compatible Veronese algebra is finite type over its complete coefficient base. -/
theorem exactVeronese_finiteType : Algebra.FiniteType (PowerSeries K)
    (CompatibleVeroneseSections K n h (exactVeroneseStep K n h)) := by
  obtain ⟨B, hB⟩ := exactVeronese_closed_lifts_from_bounded K n h
  obtain ⟨T, hT⟩ := exactVeronese_bounded_generators K n h B
  exact exactVeronese_finiteType_of_closed_generators K n h T
    (hB (Algebra.adjoin (PowerSeries K) (T : Set _)) hT)

end FLT.Mazur.PolygonInfinitesimalStages
