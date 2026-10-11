/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackSectionIdentity
public import FLT.Mazur.PolygonCompleteMarkingLineBaseChange

/-!
# Canonical marked sections after arbitrary base change

Opaque models of the actual divisor lines retain their canonical sections and
the original base-change comparison. The comparison preserves these sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeFiberMarking divisorLineBundle divisorSectionMap
  divisorLinePullbackIsoOfEq

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))

/-- The opaque line carrying the actual complete marked divisor section. -/
def completeMarkingSectionModel : (exactVeroneseProj K n h).Modules :=
  divisorLineModel _ (completeMarkingDivisor_relativeCartier K n h).1

/-- The opaque line carrying the actual lifted divisor section. -/
def completeFiberMarkingSectionModel :
    (pullback (exactVeroneseProjToBase K n h) s).Modules :=
  divisorLineModel _ (completeFiberMarkingDivisor_relativeCartier K n h s).1

/-- The complete section model is canonically the original marked line. -/
def completeMarkingSectionModelIso :
    completeMarkingSectionModel K n h ≅ completeMarkingLine K n h :=
  divisorLineModelIso (completeMarkingDivisor_relativeCartier K n h).1

/-- The lifted section model is canonically the original lifted marked line. -/
def completeFiberMarkingSectionModelIso :
    completeFiberMarkingSectionModel K n h s ≅ completeFiberMarkingLine K n h s :=
  divisorLineModelIso (completeFiberMarkingDivisor_relativeCartier K n h s).1

/-- The original canonical complete divisor section in the opaque line. -/
def completeMarkingModelSection :
    structureModule (exactVeroneseProj K n h) ⟶ completeMarkingSectionModel K n h :=
  divisorLineModelSection (completeMarkingDivisor_relativeCartier K n h).1

/-- The original canonical lifted divisor section in the opaque line. -/
def completeFiberMarkingModelSection :
    structureModule (pullback (exactVeroneseProjToBase K n h) s) ⟶
      completeFiberMarkingSectionModel K n h s :=
  divisorLineModelSection (completeFiberMarkingDivisor_relativeCartier K n h s).1

/-- The canonical base-change comparison between the opaque section models. -/
def completeMarkingSectionBaseChangeIso :
    (Scheme.Modules.pullback (pullback.fst (exactVeroneseProjToBase K n h) s)).obj
        (completeMarkingSectionModel K n h) ≅ completeFiberMarkingSectionModel K n h s :=
  @divisorLineModelPullbackIso _ _ _ _ _
    (completeMarkingDivisor_relativeCartier K n h).1
    (completeFiberMarkingDivisor_relativeCartier K n h s).1
    (completeMarkingDivisor_comap K n h s) (completeMarkingIdeal_baseChange_isIso K n h s)

/-- Arbitrary base change preserves the original canonical sections in the opaque models. -/
theorem completeMarkingSectionBaseChange_preserves :
    PullbackPreservesSection (pullback.fst (exactVeroneseProjToBase K n h) s)
      (completeMarkingSectionBaseChangeIso K n h s) (completeMarkingModelSection K n h)
      (completeFiberMarkingModelSection K n h s) :=
  @divisorLineModel_preservesSection
    (pullback (exactVeroneseProjToBase K n h) s) (exactVeroneseProj K n h)
    (pullback.fst (exactVeroneseProjToBase K n h) s)
    (completeMarkingDivisor K n h) (∏ i : Fin n, (completeFiberMarking K n h s i).ker)
    (completeMarkingDivisor_relativeCartier K n h).1
    (completeFiberMarkingDivisor_relativeCartier K n h s).1
    (completeMarkingDivisor_comap K n h s) (completeMarkingIdeal_baseChange_isIso K n h s)

end FLT.Mazur.PolygonInfinitesimalStages
