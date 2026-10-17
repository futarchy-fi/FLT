/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartSocleVanishing
public import FLT.Mazur.PolygonCompleteIdentityTopGraphBoundary
public import FLT.Mazur.PolygonCompleteIdentityFiniteLawCriterion

/-!
# The unchanged original multiplication law at every truncated stage

The full original graph has no node socle once the preceding law holds.
Its original-base flatness supplies both action boundaries and kills the
next canonical correction. Induction retains all original coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The full unchanged multiplication defect vanishes at every finite stage. -/
theorem completeIdentityFiniteMulDefect_all (m : ℕ) :
    completeIdentityFiniteMulDefect K n h 0 m = 0 := by
  induction m with
  | zero => exact completeIdentityFiniteMulDefect_zero K n h 0
  | succ m hm =>
    apply (completeIdentityFiniteLaw_iff_defect K n h 0 (m + 1)).mp
    exact completeIdentityFiniteLaw_succ_of_graphOriginalFlat K n h 0 m hm
      (completeIdentityTopGraphOriginalScalars_flat K n h m hm)

/-- The actual identity multiplication is Laurent multiplication at every finite order. -/
theorem completeIdentityFiniteLaw_all (m : ℕ) :
    universalEdgeScaling (Ring K m) ≫ completeIdentityStageTorus K n h 0 m =
      completeIdentityFiniteOriginalMul K n h 0 m :=
  (completeIdentityFiniteLaw_iff_defect K n h 0 m).mpr
    (completeIdentityFiniteMulDefect_all K n h m)

/-- Every canonical higher correction of the unchanged identity multiplication vanishes. -/
theorem completeIdentityTopCorrection_all_zero (m : ℕ) :
    completeIdentityTopCorrection K n h 0 m = 0 :=
  (completeIdentityFiniteLaw_succ_iff_correction K n h 0 m
    (completeIdentityFiniteMulDefect_all K n h m)).mp
      (completeIdentityFiniteLaw_all K n h (m + 1))

/-- In particular, the previously open second canonical correction is zero. -/
theorem completeIdentitySecondCorrection_zero :
    completeIdentityTopCorrection K n h 0 1 = 0 :=
  completeIdentityTopCorrection_all_zero K n h 1

/-- The same original comparison holds over each whole finite polygon, including its nodes. -/
theorem completeIdentityFiniteComparison_all (m : ℕ) :
    completeIdentityFiniteScaling K n h m ≫ completePointToIntegralCubic K n h 0 =
      completeIdentityFiniteInput K n h 0 m ≫ completeIdentityActionTarget K n h 0 :=
  (completeIdentityFiniteComparison_iff_laurentLaw K n h m).mpr
    (completeIdentityFiniteLaw_all K n h m)

end FLT.Mazur.PolygonInfinitesimalStages
