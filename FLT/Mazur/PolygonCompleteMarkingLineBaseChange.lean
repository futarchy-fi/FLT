/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteMarkingAmple
public import FLT.Mazur.RelativeSectionAmpleBaseChange

/-!
# The ample complete marked line under arbitrary base change

The line of the actual lifted marking ideals is canonically the pullback of
the original complete marked line. This transports relative ampleness
over every new scheme base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeMarkingDivisor completeFiberMarking

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))

/-- The positive line of the actual lifted marked divisor. -/
def completeFiberMarkingLine : (pullback (exactVeroneseProjToBase K n h) s).Modules :=
  divisorLineBundle (∏ i : Fin n, (completeFiberMarking K n h s i).ker)
    (completeFiberMarkingDivisor_relativeCartier K n h s).1

/-- The complete ideal comparison remains invertible on every new base. -/
instance completeMarkingIdeal_baseChange_isIso :
    IsIso (idealModulePullbackHom (completeMarkingDivisor K n h)
      (pullback.fst (exactVeroneseProjToBase K n h) s)) := by
  apply idealModulePullbackHom_isIso_of_cartier _
    (completeMarkingDivisor_relativeCartier K n h).1
  rw [completeMarkingDivisor_comap]
  exact (completeFiberMarkingDivisor_relativeCartier K n h s).1

/-- The actual lifted marked line is the canonical pullback of the complete marked line. -/
def completeMarkingLineBaseChangeIso :
    (Scheme.Modules.pullback (pullback.fst (exactVeroneseProjToBase K n h) s)).obj
        (completeMarkingLine K n h) ≅ completeFiberMarkingLine K n h s :=
  divisorLinePullbackIsoOfEq _ (completeMarkingDivisor_relativeCartier K n h).1
    (completeFiberMarkingDivisor_relativeCartier K n h s).1
    (completeMarkingDivisor_comap K n h s)

/-- The actual lifted marked line is relatively ample after every scheme base change. -/
theorem completeFiberMarkingLine_relativelyAmple :
    RelativelyAmpleLineBundle (pullback.snd (exactVeroneseProjToBase K n h) s)
      (completeFiberMarkingLine K n h s) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  exact ((completeMarkingLine_relativelyAmple K n h).baseChange s).of_iso
    (completeMarkingLineBaseChangeIso K n h s).symm

end FLT.Mazur.PolygonInfinitesimalStages
