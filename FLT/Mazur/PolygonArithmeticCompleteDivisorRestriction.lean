/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompleteDivisor
public import FLT.Mazur.PolygonArithmeticCompleteStageIdeals
public import FLT.Mazur.PolygonArithmeticBoundaryDivisor

/-!
# The complete marked divisor restricts to every original stage divisor

Restriction preserves the actual product of the section ideals. In particular
the complete divisor realizes the same unit-one boundary divisor used to
construct the original finite-stage boundary line bundles.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The complete divisor restricts to the actual product of the original marked section ideals. -/
theorem completeMarkingDivisor_originalStage (m : ℕ) :
    (completeMarkingDivisor A π hne hgen n h).comap
      (originalStageToCompatibleProj A π hne hgen n h m) =
      ∏ i : Fin n, (marking A π m n h i).ker := by
  simp only [completeMarkingDivisor, FCurve.idealSheaf_comap_prod,
    completeBaseMarking_ker_originalStage]

/-- Every original unit-one boundary divisor is the restriction of the actual complete divisor. -/
theorem completeMarkingDivisor_originalBoundary (m : ℕ) :
    (completeMarkingDivisor A π hne hgen n h).comap
      (originalStageToCompatibleProj A π hne hgen n h m) =
      boundaryIdeal A π m n h := by
  exact completeMarkingDivisor_originalStage A π hne hgen n h m

end FLT.Mazur.PolygonArithmeticStages
