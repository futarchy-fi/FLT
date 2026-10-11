/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicQuotientSpectrum
public import FLT.Mazur.PolygonStageRetainedBaseComparison
public import FLT.Mazur.PolygonCompleteMarkingSpecialization

/-!
# The original coefficient stages retain the actual base-ideal powers

The original truncated coefficient map has exactly the parameter-power
kernel. Its zero stage contains the closed point of the complete local base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

/-- The actual base-stage map has the original parameter-power ideal sheaf as kernel. -/
theorem baseToSeries_ker (m : ℕ) :
    (baseToSeries K m).ker =
      BaseAdicThickening.baseIdeal (.of (PowerSeries K)) (parameterIdeal K) ^ (m + 1) := by
  rw [← stageAdicBaseIso_toSeries K m, Scheme.Hom.ker_comp_of_isIso]
  exact (BaseAdicThickening.quotientSpec_ker (.of (PowerSeries K))
    (parameterIdeal K ^ (m + 1))).trans
    (BaseAdicThickening.baseIdeal_pow _ _ _)

/-- The retained parameter ideal contains the unique closed base point in its support. -/
theorem completeParameterBaseIdeal_closedPoint :
    IsLocalRing.closedPoint (PowerSeries K) ∈
      (BaseAdicThickening.baseIdeal (.of (PowerSeries K)) (parameterIdeal K)).support := by
  have hk := baseToSeries_ker K 0
  simp only [zero_add, pow_one] at hk
  rw [← hk]
  exact (baseToSeries K 0).range_subset_ker_support
    ⟨stageBasePoint K 0, baseToSeries_stageBasePoint K 0⟩

end FLT.Mazur.PolygonInfinitesimalStages
