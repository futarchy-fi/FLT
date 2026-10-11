/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingDivisor
public import FLT.Mazur.PolygonCompleteStageMarkings
public import FLT.Mazur.PolygonInfinitesimalDivisor

/-!
# The complete marked divisor restricts to every original stage divisor

Restriction preserves the actual product of the section ideals. In particular
the complete divisor realizes the same unit-one boundary divisor used to
construct the original finite-stage boundary line bundles.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The complete divisor restricts to the actual product of the original marked section ideals. -/
theorem completeMarkingDivisor_originalStage (m : ℕ) :
    (completeMarkingDivisor K n h).comap (originalStageToCompatibleProj K n h m) =
      ∏ i : Fin n, (marking K m n h i).ker := by
  simp only [completeMarkingDivisor, FCurve.idealSheaf_comap_prod,
    completeBaseMarking_ker_originalStage]

/-- Every original unit-one boundary divisor is the restriction of the actual complete divisor. -/
theorem completeMarkingDivisor_originalBoundary (m : ℕ) :
    (completeMarkingDivisor K n h).comap (originalStageToCompatibleProj K n h m) =
      PolygonInfinitesimal.markingDivisor (Ring K m) (parameter K m) n h (fun _ ↦ 1) := by
  exact completeMarkingDivisor_originalStage K n h m

end FLT.Mazur.PolygonInfinitesimalStages
