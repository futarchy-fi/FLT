/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.GradedProjDedekindFlatness
public import FLT.Mazur.PolygonArithmeticCoefficientFlatness
public import FLT.Mazur.PolygonArithmeticMarkingSpecialization

/-!
# Flatness of the original arithmetic polygon candidate

The actual compatible Veronese algebra is flat over the original local domain.
Its homogeneous-localization charts prove flatness of the same structural map
whose adic fibers recover the original arithmetic stages.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual arithmetic candidate is flat over its original coefficient ring. -/
theorem exactVeroneseProjToBase_flat :
    Flat (exactVeroneseProjToBase A π n h hne hgen) := by
  let _ := LocalParameterFlatness.isDedekindDomain A π hgen
  let _ := compatibleVeronese_flat A π hne hgen n h (exactVeroneseStep A π hne hgen n h)
  exact GradedProjDedekindFlatness.toSpecBase_flat
    (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h))

variable [IsAdicComplete (ideal A π) A]

/-- Each actual complete arithmetic marking is a closed immersion into the proper candidate. -/
theorem completeBaseMarking_isClosedImmersion (i : Fin n) :
    IsClosedImmersion (completeBaseMarking A π hne hgen n h i) := by
  let _ := exactVeroneseProjToBase_isProper A π n h hne hgen
  exact LocalBaseSectionDisjointness.section_isClosedImmersion
    (exactVeroneseProjToBase A π n h hne hgen) _
    (completeBaseMarking_toBase A π hne hgen n h i)

end FLT.Mazur.PolygonArithmeticStages
