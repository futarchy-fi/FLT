/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartPullbackFaithful
public import FLT.Mazur.SchemeFppfSourceLineGluing

/-!
# Faithful fppf pullback on actual line bundles

The constructed affine charts cover the base. Their faithful flatness
therefore detects any morphism between line bundles after fppf pullback.
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

/-- An fppf pullback detects equality between morphisms of actual line bundles. -/
lemma fppfLine_pullback_map_injective {M N : X.Modules}
    (hM : LocallyFreeRankOne M) (hN : LocallyFreeRankOne N) (f g : M ⟶ N)
    (h : (pullback p).map f = (pullback p).map g) : f = g := by
  let _ : ∀ y, ((pullback (fppfSourceCharts p y).chart.base).obj M).IsQuasicoherent :=
    fun y ↦ by
      let _ := SchemePicard.rankOne_finitePresentation _
        (hM.pullback (fppfSourceCharts p y).chart.base)
      infer_instance
  let _ : ∀ y, ((pullback (fppfSourceCharts p y).chart.base).obj N).IsQuasicoherent :=
    fun y ↦ by
      let _ := SchemePicard.rankOne_finitePresentation _
        (hN.pullback (fppfSourceCharts p y).chart.base)
      infer_instance
  apply chartFamily_pullback_map_injective (fun y ↦ (fppfSourceCharts p y).chart) _ f g h
  intro x
  have hx : x ∈ iSup (fun y ↦ (fppfSourceCharts p y).chart.base.opensRange) := by
    rw [fppfSourceCharts_baseCovers p]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

end FLT.Mazur.SchemeAffineDescent
