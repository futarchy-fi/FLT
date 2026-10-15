/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LocalParameterFlatness
public import FLT.Mazur.PolygonArithmeticParameterRegularity
public import FLT.Mazur.PolygonArithmeticVeronese

/-!
# Flatness of the actual compatible graded coefficient modules

The previously proved parameter regularity upgrades to flatness over the
original Noetherian local domain, both in each original degree and in every retained Veronese.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  (n : ℕ) (h : 2 ≤ n)

include hne hgen in
/-- Every original compatible homogeneous degree is flat over the complete coefficient ring. -/
theorem compatibleDegree_flat (d : ℕ) :
    Module.Flat A (compatibleSectionDegree A π n h d) :=
  LocalParameterFlatness.flat A π hgen _ (compatibleDegree_parameter_eq_zero A π hne n h d) hne

include hne hgen in
/-- The full finite-degree-support algebra is flat over its original arithmetic scalars. -/
theorem compatibleGraded_flat : Module.Flat A (CompatibleGradedSections A π n h) :=
  LocalParameterFlatness.flat A π hgen _ (compatibleGraded_parameter_eq_zero A π hne n h) hne

omit [IsLocalRing A] in
include hne in
/-- The retained Veronese algebra has regular parameter, in its original scalar structure. -/
theorem compatibleVeronese_parameter_eq_zero (q : ℕ) (s : CompatibleVeroneseSections A π n h q)
    (hs : π • s = 0) : s = 0 := by
  apply DFinsupp.ext
  intro d
  apply compatibleDegree_parameter_eq_zero A π hne n h (q * d)
  exact congrArg (fun t : CompatibleVeroneseSections A π n h q ↦ t d) hs

include hne hgen in
/-- Every retained Veronese algebra is torsion-free over the original complete base. -/
theorem compatibleVeronese_isTorsionFree (q : ℕ) :
    Module.IsTorsionFree A (CompatibleVeroneseSections A π n h q) :=
  LocalParameterFlatness.isTorsionFree A π hgen _
    (compatibleVeronese_parameter_eq_zero A π hne n h q) hne

include hne hgen in
/-- Every retained Veronese algebra is flat over the original complete base. -/
theorem compatibleVeronese_flat (q : ℕ) :
    Module.Flat A (CompatibleVeroneseSections A π n h q) :=
  LocalParameterFlatness.flat A π hgen _ (compatibleVeronese_parameter_eq_zero A π hne n h q) hne

end FLT.Mazur.PolygonArithmeticStages
