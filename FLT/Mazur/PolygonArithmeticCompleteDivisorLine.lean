/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCompleteDivisorRestriction
public import FLT.Mazur.PolygonArithmeticBoundaryLine

/-!
# The complete marked line and its original stage restrictions

Dualizing the actual complete marking ideal gives a coherent line. Its canonical
pullback comparison identifies every original stage with the original boundary
line and preserves the actual divisor section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The positive line of the actual complete marked divisor. -/
def completeMarkingLine : (exactVeroneseProj A π n h hne hgen).Modules :=
  divisorLineBundle (completeMarkingDivisor A π hne hgen n h)
    (completeMarkingDivisor_relativeCartier A π hne hgen n h).1

/-- The complete marked line is locally free of rank one. -/
theorem completeMarkingLine_rankOne : LocallyFreeRankOne (completeMarkingLine A π hne hgen n h) :=
  (completeMarkingDivisor_relativeCartier A π hne hgen n h).1.divisorLineBundle_locallyFreeRankOne

/-- The complete marked line is coherent. -/
theorem completeMarkingLine_isFinitePresentation :
    (completeMarkingLine A π hne hgen n h).IsFinitePresentation :=
  (completeMarkingLine_rankOne A π hne hgen n h).isFinitePresentation

/-- The canonical ideal comparison is invertible at every original stage. -/
instance completeMarkingIdeal_stage_isIso (m : ℕ) :
    IsIso (idealModulePullbackHom (completeMarkingDivisor A π hne hgen n h)
      (originalStageToCompatibleProj A π hne hgen n h m)) := by
  apply idealModulePullbackHom_isIso_of_cartier _
    (completeMarkingDivisor_relativeCartier A π hne hgen n h).1
  rw [completeMarkingDivisor_originalBoundary]
  exact (boundaryIdeal_cartier A π m n h).1

/-- The complete marking line restricts canonically to the original boundary line. -/
def completeMarkingLineStageIso (m : ℕ) :
    (pullback (originalStageToCompatibleProj A π hne hgen n h m)).obj
      (completeMarkingLine A π hne hgen n h) ≅
      boundaryLine A π m n h :=
  divisorLinePullbackIsoOfEq _ (completeMarkingDivisor_relativeCartier A π hne hgen n h).1
    (boundaryIdeal_cartier A π m n h).1 (completeMarkingDivisor_originalBoundary A π hne hgen n h m)

/-- The comparison retains the actual canonical divisor section. -/
@[reassoc] theorem completeMarkingLineStageIso_section (m : ℕ) :
    (pullback (originalStageToCompatibleProj A π hne hgen n h m)).map
        (divisorSectionMap (completeMarkingDivisor_relativeCartier A π hne hgen n h).1) ≫
      (completeMarkingLineStageIso A π hne hgen n h m).hom =
        (modulePullbackUnitIso (originalStageToCompatibleProj A π hne hgen n h m)).hom ≫
          divisorSectionMap (boundaryIdeal_cartier A π m n h).1 :=
  divisorLinePullbackIsoOfEq_section _ (completeMarkingDivisor_relativeCartier A π hne hgen n h).1
    (boundaryIdeal_cartier A π m n h).1 (completeMarkingDivisor_originalBoundary A π hne hgen n h m)

end FLT.Mazur.PolygonArithmeticStages
