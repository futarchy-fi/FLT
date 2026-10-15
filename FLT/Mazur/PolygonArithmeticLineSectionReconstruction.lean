/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicSectionProjectionExt
public import FLT.Mazur.BaseAdicSectionSuccessorReconstruction
public import FLT.Mazur.PolygonArithmeticCompleteLineQuotient

/-!
# Formal section reconstruction over the original complete arithmetic base

Proper formal functions applies to every actual line on the complete polygon.
The original pullback transitions, not replacement quotient transitions, express
compatibility. In particular all original restrictions jointly detect a section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonArithmeticStages

open FCurve IdealAdicQuotient

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] originalStageToCompatibleProj family
  exactVeroneseProj exactVeroneseProjToBase
  completeLineStageTransitionIso

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π)
  [IsAdicComplete (ideal A π) A] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : (exactVeroneseProj A π n h hne hgen).Modules) (hL : LocallyFreeRankOne L)

/-- Compatible positive quotients reconstruct a unique section of any complete line. -/
theorem completeLineSection_existsUnique :
    let _ := hL.isFinitePresentation
    ∀ s : ∀ m, Γ(quotient (compatibleProjAdicIdeal A π hne hgen n h) L (m + 1), ⊤),
      (∀ a b (hab : a ≤ b),
        (IdealAdicQuotient.reduction (compatibleProjAdicIdeal A π hne hgen n h) L
          (Nat.add_le_add_right hab 1)).app ⊤
          (s b) = s a) →
      ∃! t : Γ(L, ⊤), ∀ m,
        (projection (compatibleProjAdicIdeal A π hne hgen n h) L (m + 1)).app ⊤ t = s m := by
  let _ : (exactVeroneseProj A π n h hne hgen).IsSeparated :=
    inferInstanceAs (Proj (compatibleVeroneseGrade A π n h
      (exactVeroneseStep A π hne hgen n h))).IsSeparated
  let _ := exactVeroneseProjToBase_isProper A π n h hne hgen
  let _ := hL.isFinitePresentation
  exact BaseAdicCohomology.existsUnique_globalSection_succ
    (exactVeroneseProjToBase A π n h hne hgen) (ideal A π) L

include hL

/-- All original finite-stage restrictions jointly detect actual complete line sections. -/
theorem completeLineSection_ext (s t : Γ(L, ⊤))
    (hst : ∀ m, pullGlobal (originalStageToCompatibleProj A π hne hgen n h m) L s =
      pullGlobal (originalStageToCompatibleProj A π hne hgen n h m) L t) : s = t := by
  let _ := hL.isFinitePresentation
  exact section_ext_of_quotient_iso (compatibleProjAdicIdeal A π hne hgen n h) L
    (fun m ↦ (pushforward (originalStageToCompatibleProj A π hne hgen n h m)).obj
      (completeLineOnStage A π hne hgen n h L m))
    (completeLineQuotientStageIso A π hne hgen n h L hL)
    (fun m ↦ (pullbackPushforwardAdjunction
      (originalStageToCompatibleProj A π hne hgen n h m)).unit.app L)
    (projection_completeLineQuotientStageIso A π hne hgen n h L hL)
    (completeLineSection_existsUnique A π hne hgen n h L hL) s t hst

end FLT.Mazur.PolygonArithmeticStages
