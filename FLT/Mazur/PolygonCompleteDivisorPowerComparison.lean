/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteDivisorLine
public import FLT.Mazur.PolygonCompleteBoundaryLineComparison
public import FLT.Mazur.PolygonCompleteLineQuotient

/-!
# Marked divisor powers and the complete coefficient line on every original stage

Each actual complete divisor power restricts to the original boundary power.
At the chosen coefficient exponent this compares the two complete lines on
every original stage. These are finite-stage comparisons, not a global isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj family boundaryLine completeMarkingLine
  completeCoefficientLine ModuleSheafTensor.tensor completeCoefficientBoundaryIso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Every complete marked tensor power restricts to its original boundary power. -/
def completeMarkingPowerStageIso (d m : ℕ) :
    (pullback (originalStageToCompatibleProj K n h m)).obj
        (tensorPower (completeMarkingLine K n h) d) ≅
      tensorPower (boundaryLine K m n h) d :=
  tensorPowerIso _ _ d ≪≫ tensorPowerCongr (completeMarkingLineStageIso K n h m) d

/-- The coefficient line and the actual marked power agree on every original finite stage. -/
def completeCoefficientMarkingStageIso (m : ℕ) :
    (pullback (originalStageToCompatibleProj K n h m)).obj (completeCoefficientLine K n h) ≅
      (pullback (originalStageToCompatibleProj K n h m)).obj
        (tensorPower (completeMarkingLine K n h) (completeCoefficientBoundaryExponent K n h)) :=
  completeCoefficientBoundaryIso K n h m ≪≫
    (completeMarkingPowerStageIso K n h (completeCoefficientBoundaryExponent K n h) m).symm

/-- Comparison with the actual marked power retains the original coefficient comparison. -/
@[reassoc] theorem completeCoefficientMarkingStageIso_boundary (m : ℕ) :
    (completeCoefficientMarkingStageIso K n h m).hom ≫
      (completeMarkingPowerStageIso K n h (completeCoefficientBoundaryExponent K n h) m).hom =
        (completeCoefficientBoundaryIso K n h m).hom := by
  simp only [completeCoefficientMarkingStageIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every positive quotient of the marked power is an original boundary power. -/
def completeMarkingPowerQuotientIso (d m : ℕ) :
    IdealAdicQuotient.quotient (compatibleProjAdicIdeal K n h)
        (tensorPower (completeMarkingLine K n h) d) (m + 1) ≅
      (pushforward (originalStageToCompatibleProj K n h m)).obj
        (tensorPower (boundaryLine K m n h) d) :=
  completeLineQuotientStageIso K n h _ ((completeMarkingLine_rankOne K n h).tensorPower d) m ≪≫
    (pushforward (originalStageToCompatibleProj K n h m)).mapIso
      (completeMarkingPowerStageIso K n h d m)

/-- Quotient projection is the original marked-power restriction. -/
@[reassoc] theorem projection_completeMarkingPowerQuotientIso (d m : ℕ) :
    IdealAdicQuotient.projection (compatibleProjAdicIdeal K n h)
        (tensorPower (completeMarkingLine K n h) d) (m + 1) ≫
      (completeMarkingPowerQuotientIso K n h d m).hom =
        (pullbackPushforwardAdjunction (originalStageToCompatibleProj K n h m)).unit.app _ ≫
          (pushforward (originalStageToCompatibleProj K n h m)).map
            (completeMarkingPowerStageIso K n h d m).hom := by
  rw [completeMarkingPowerQuotientIso, Iso.trans_hom, Functor.mapIso_hom,
    projection_completeLineQuotientStageIso_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
