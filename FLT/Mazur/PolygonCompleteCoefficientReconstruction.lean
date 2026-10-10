/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicSectionSuccessorReconstruction
public import FLT.Mazur.PolygonCompleteCoefficientLine
public import FLT.Mazur.PolygonCompleteLineQuotient

/-!
# Reconstruction for the actual complete coefficient line

The constructed coherent line satisfies proper formal functions over the
original power-series base. Its positive adic quotients are the pushforwards
of actual pullbacks along the original polygon stage maps.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules
open FLT.Mazur.FCurve

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The coefficient line restricts to a line on each original polygon stage. -/
theorem completeCoefficientLineOnStage_rankOne (m : ℕ) :
    LocallyFreeRankOne (completeLineOnStage K n h (completeCoefficientLine K n h) m) :=
  (completeCoefficientLine_rankOne K n h).pullback (originalStageToCompatibleProj K n h m)

/-- The actual coefficient quotient is the original stage pullback, pushed forward. -/
def completeCoefficientQuotientStageIso (m : ℕ) :
    IdealAdicQuotient.quotient (compatibleProjAdicIdeal K n h)
        (completeCoefficientLine K n h) (m + 1) ≅
      (pushforward (originalStageToCompatibleProj K n h m)).obj
        (completeLineOnStage K n h (completeCoefficientLine K n h) m) :=
  completeLineQuotientStageIso K n h _ (completeCoefficientLine_rankOne K n h) m

/-- The coefficient comparison retains the actual original stage restriction. -/
@[reassoc] theorem projection_completeCoefficientQuotientStageIso (m : ℕ) :
    IdealAdicQuotient.projection (compatibleProjAdicIdeal K n h)
        (completeCoefficientLine K n h) (m + 1) ≫
      (completeCoefficientQuotientStageIso K n h m).hom =
        (pullbackPushforwardAdjunction (originalStageToCompatibleProj K n h m)).unit.app
          (completeCoefficientLine K n h) :=
  projection_completeLineQuotientStageIso K n h _ (completeCoefficientLine_rankOne K n h) m

/-- Compatible positive quotient sections reconstruct a unique actual coefficient section. -/
theorem completeCoefficientSection_existsUnique :
    let _ := completeCoefficientLine_isFinitePresentation K n h
    ∀ s : ∀ m, Γ(IdealAdicQuotient.quotient (compatibleProjAdicIdeal K n h)
      (completeCoefficientLine K n h) (m + 1), ⊤),
      (∀ a b (hab : a ≤ b),
        (IdealAdicQuotient.reduction (compatibleProjAdicIdeal K n h)
          (completeCoefficientLine K n h) (Nat.add_le_add_right hab 1)).app ⊤ (s b) = s a) →
      ∃! t : Γ(completeCoefficientLine K n h, ⊤), ∀ m,
        (IdealAdicQuotient.projection (compatibleProjAdicIdeal K n h)
          (completeCoefficientLine K n h) (m + 1)).app ⊤ t = s m := by
  let _ : (exactVeroneseProj K n h).IsSeparated :=
    inferInstanceAs (Proj (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))).IsSeparated
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := completeCoefficientLine_isFinitePresentation K n h
  exact BaseAdicCohomology.existsUnique_globalSection_succ (exactVeroneseProjToBase K n h)
    (parameterIdeal K) (completeCoefficientLine K n h)

end FLT.Mazur.PolygonInfinitesimalStages
