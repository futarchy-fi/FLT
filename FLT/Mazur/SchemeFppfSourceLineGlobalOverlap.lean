/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSourceGlobalOverlap
public import FLT.Mazur.SchemeFppfSourceLineGlobalRecovery

/-!
# Original overlap compatibility for fppf line-bundle recovery

The actual constructed fppf line-bundle recovery identifies the supplied
descent overlap with its reconstructed canonical overlap.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open FCurve SchemePullbackOverlap
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (hM : LocallyFreeRankOne M)

/-- The original descent overlap is exactly the one induced by global fppf recovery. -/
lemma fppfSourceLineGlobalRecoveryIso_overlap :
    D.overlap = chartOverlap p (Limits.pullback.fst p p) (Limits.pullback.snd p p)
      (Limits.pullback.fst p p ≫ p) rfl Limits.pullback.condition.symm
      (fppfSourceLineGlued p D hM) (fppfSourceLineGlobalRecoveryIso p D hM) := by
  let _ := fppfSourceCharts_quasicoherent p hM
  exact sourceGluedRecoveryIso_overlap (fppfSourceCharts p) D
    (fun y ↦ ⟨y, fppfSourceCharts_mem p y⟩)

end FLT.Mazur.SchemeAffineDescent
