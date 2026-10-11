/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSectionProjectionExt
public import FLT.Mazur.BaseAdicSectionSuccessorReconstruction
public import FLT.Mazur.PolygonCompleteLineOriginalReduction

/-!
# Reconstruction of any complete line from original stage sections

Proper formal functions applies to every actual line on the complete polygon.
The original pullback transitions, not replacement quotient transitions, express
compatibility. In particular all original restrictions jointly detect a section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve IdealAdicQuotient

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] originalStageToCompatibleProj family
  exactVeroneseProj exactVeroneseProjToBase
  completeLineStageTransitionIso

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj K n h).Modules) (hL : LocallyFreeRankOne L)

/-- Compatible positive quotients reconstruct a unique section of any complete line. -/
theorem completeLineSection_existsUnique :
    let _ := hL.isFinitePresentation
    ∀ s : ∀ m, Γ(quotient (compatibleProjAdicIdeal K n h) L (m + 1), ⊤),
      (∀ a b (hab : a ≤ b),
        (IdealAdicQuotient.reduction (compatibleProjAdicIdeal K n h) L
          (Nat.add_le_add_right hab 1)).app ⊤
          (s b) = s a) →
      ∃! t : Γ(L, ⊤), ∀ m,
        (projection (compatibleProjAdicIdeal K n h) L (m + 1)).app ⊤ t = s m := by
  let _ : (exactVeroneseProj K n h).IsSeparated :=
    inferInstanceAs (Proj (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))).IsSeparated
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := hL.isFinitePresentation
  exact BaseAdicCohomology.existsUnique_globalSection_succ
    (exactVeroneseProjToBase K n h) (parameterIdeal K) L

include hL

/-- All original finite-stage restrictions jointly detect actual complete line sections. -/
theorem completeLineSection_ext (s t : Γ(L, ⊤))
    (hst : ∀ m, pullGlobal (originalStageToCompatibleProj K n h m) L s =
      pullGlobal (originalStageToCompatibleProj K n h m) L t) : s = t := by
  let _ := hL.isFinitePresentation
  exact section_ext_of_quotient_iso (compatibleProjAdicIdeal K n h) L
    (fun m ↦ (pushforward (originalStageToCompatibleProj K n h m)).obj
      (completeLineOnStage K n h L m))
    (completeLineQuotientStageIso K n h L hL)
    (fun m ↦ (pullbackPushforwardAdjunction (originalStageToCompatibleProj K n h m)).unit.app L)
    (projection_completeLineQuotientStageIso K n h L hL)
    (completeLineSection_existsUnique K n h L hL) s t hst

end FLT.Mazur.PolygonInfinitesimalStages
