/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjDedekindFlatness
public import FLT.Mazur.PolygonCompatibleCoefficientFlatness
public import FLT.Mazur.PolygonCompleteMarkingSpecialization

/-!
# Flatness of the actual complete-base polygon candidate

The original compatible Veronese algebra is flat over the power-series DVR.
Its actual homogeneous-localization charts inherit flatness, proving flatness
of the same structural morphism used in the finite-stage realization.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual complete-base candidate is flat over its original power-series structural map. -/
theorem exactVeroneseProjToBase_flat : Flat (exactVeroneseProjToBase K n h) := by
  let _ := compatibleVeronese_flat K n h (exactVeroneseStep K n h)
  exact GradedProjDedekindFlatness.toSpecBase_flat
    (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))

/-- Each actual complete marking is a closed immersion into the proper candidate. -/
theorem completeBaseMarking_isClosedImmersion (i : Fin n) :
    IsClosedImmersion (completeBaseMarking K n h i) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact LocalBaseSectionDisjointness.section_isClosedImmersion
    (exactVeroneseProjToBase K n h) _ (completeBaseMarking_toBase K n h i)

end FLT.Mazur.PolygonInfinitesimalStages
