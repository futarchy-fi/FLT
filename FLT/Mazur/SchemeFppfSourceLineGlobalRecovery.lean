/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSourceGlobalRecovery
public import FLT.Mazur.SchemeFppfSourceLineMap

/-!
# Global recovery and naturality for fppf line bundles

Glue the proved compatible original source recoveries. The resulting
isomorphism retains source-chart equations and is natural in compatible maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (hM : LocallyFreeRankOne M)

/-- Effective object reconstruction on the original fppf covering scheme. -/
def fppfSourceLineGlobalRecoveryIso :
    (pullback p).obj (fppfSourceLineGlued p D hM) ≅ M := by
  let _ := fppfSourceCharts_quasicoherent p hM
  exact sourceGluedRecoveryIso (fppfSourceCharts p) D
    (fun y ↦ ⟨y, fppfSourceCharts_mem p y⟩)

/-- Global fppf recovery retains the given reconstruction on every source chart. -/
lemma fppfSourceLineGlobalRecoveryIso_pullback (y : Y) :
    (pullback (fppfSourceCharts p y).sourceMap).map
        (fppfSourceLineGlobalRecoveryIso p D hM).hom =
      (fppfSourceLineRecoveryIso p D hM y).hom := by
  let _ := fppfSourceCharts_quasicoherent p hM
  exact sourceGluedRecoveryIso_pullback (fppfSourceCharts p) D
    (fun y ↦ ⟨y, fppfSourceCharts_mem p y⟩) y

/-- The constructed global recovery is natural in every compatible line-bundle map. -/
@[reassoc]
lemma fppfSourceLineGlobalRecoveryIso_naturality {N : Y.Modules}
    (E : SchemeGeometricDescent.Data p N) (hN : LocallyFreeRankOne N)
    (f : M ⟶ N) (hf : D.MapCompatible p E f) :
    (pullback p).map (fppfSourceLineMap p D E hM hN f hf) ≫
        (fppfSourceLineGlobalRecoveryIso p E hN).hom =
      (fppfSourceLineGlobalRecoveryIso p D hM).hom ≫ f := by
  apply ModuleSheafOpenImmersionGluing.hom_ext
    (fun y ↦ (fppfSourceCharts p y).source)
    (fun y ↦ (fppfSourceCharts p y).sourceMap)
    (fun y ↦ ⟨y, fppfSourceCharts_mem p y⟩)
  intro y
  rw [Functor.map_comp, Functor.map_comp,
    fppfSourceLineGlobalRecoveryIso_pullback, fppfSourceLineGlobalRecoveryIso_pullback]
  exact fppfSourceLineMap_recovery p D E hM hN f hf y

end FLT.Mazur.SchemeAffineDescent
