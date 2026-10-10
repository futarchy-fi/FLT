/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerSeriesParameterFlatness
public import FLT.Mazur.PolygonCompatibleParameterRegularity
public import FLT.Mazur.PolygonCompatibleVeronese

/-!
# Flatness of the actual compatible graded coefficient modules

The previously proved parameter regularity upgrades to flatness over the
power-series DVR, both in each original degree and in every retained Veronese.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n)

/-- Every original compatible homogeneous degree is flat over the complete coefficient ring. -/
theorem compatibleDegree_flat (d : ℕ) :
    Module.Flat (PowerSeries K) (compatibleSectionDegree K n h d) :=
  PowerSeriesParameterFlatness.flat K _ (compatibleDegree_parameter_eq_zero K n h d)

/-- The full finite-degree-support algebra is flat over its original power-series scalars. -/
theorem compatibleGraded_flat : Module.Flat (PowerSeries K) (CompatibleGradedSections K n h) :=
  PowerSeriesParameterFlatness.flat K _ (compatibleGraded_parameter_eq_zero K n h)

/-- The retained Veronese algebra has regular parameter, in its original scalar structure. -/
theorem compatibleVeronese_parameter_eq_zero (q : ℕ) (s : CompatibleVeroneseSections K n h q)
    (hs : (PowerSeries.X : PowerSeries K) • s = 0) : s = 0 := by
  apply DFinsupp.ext
  intro d
  apply compatibleDegree_parameter_eq_zero K n h (q * d)
  exact congrArg (fun t : CompatibleVeroneseSections K n h q ↦ t d) hs

/-- Every retained Veronese algebra is torsion-free over the original complete base. -/
theorem compatibleVeronese_isTorsionFree (q : ℕ) :
    Module.IsTorsionFree (PowerSeries K) (CompatibleVeroneseSections K n h q) :=
  PowerSeriesParameterFlatness.isTorsionFree K _ (compatibleVeronese_parameter_eq_zero K n h q)

/-- Every retained Veronese algebra is flat over the original complete base. -/
theorem compatibleVeronese_flat (q : ℕ) :
    Module.Flat (PowerSeries K) (CompatibleVeroneseSections K n h q) :=
  PowerSeriesParameterFlatness.flat K _ (compatibleVeronese_parameter_eq_zero K n h q)

end FLT.Mazur.PolygonInfinitesimalStages
