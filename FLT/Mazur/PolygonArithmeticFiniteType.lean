/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticBoundedGenerators
public import FLT.Mazur.PolygonArithmeticClosedLifts
public import FLT.Mazur.PolygonArithmeticClosedGeneration

/-!
# Finite type of the actual compatible Veronese algebra

Finite compatible generators in bounded degrees lift every closed section
by the proved multiplication recurrence. Degreewise Nakayama then proves
that they generate the entire original compatible Veronese algebra over
the original complete integral base, with no closed-generation hypothesis.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] compatibleEval boundaryLine family boundaryIntegralScalars
attribute [local irreducible] Algebra.adjoin

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n] [IsAdicComplete (ideal A π) A]

/-- The original compatible Veronese algebra is finite type over its complete coefficient base. -/
theorem exactVeronese_finiteType : Algebra.FiniteType (A)
    (CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)) := by
  obtain ⟨B, hB⟩ := exactVeronese_closed_lifts_from_bounded A π hne hgen n h
  obtain ⟨T, hT⟩ := exactVeronese_bounded_generators A π hne hgen n h B
  exact exactVeronese_finiteType_of_closed_generators A π hne hgen n h T
    (hB (Algebra.adjoin A (T : Set _)) hT)

end FLT.Mazur.PolygonArithmeticStages
