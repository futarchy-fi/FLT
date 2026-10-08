/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineFppfSourceCover
public import FLT.Mazur.SchemeAffineSourceRecovery
public import FLT.Mazur.SchemeAffineOpenGluingLine

/-!
# Fppf line-bundle gluing with a covering source reconstruction

Use the chart family that covers both source and base. Its glued line
bundle reconstructs the original object on actual source opens covering
the whole covering scheme. Compatibility of these local isomorphisms
remains the input to global reconstruction, not an assumed field here.
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

include hM in
/-- Local quasi-coherence follows from the original line bundle on every source chart. -/
lemma fppfSourceCharts_quasicoherent (y : Y) :
    ((pullback (fppfSourceCharts p y).chart.cover).obj M).IsQuasicoherent := by
  let _ := SchemePicard.rankOne_finitePresentation _
    (hM.pullback (fppfSourceCharts p y).chart.cover)
  infer_instance

/-- The line-bundle candidate using the chart family with a covering source refinement. -/
def fppfSourceLineGlued : X.Modules := by
  let _ := fppfSourceCharts_quasicoherent p hM
  exact openGlued (fun y ↦ (fppfSourceCharts p y).chart) D

/-- The constructed candidate is an actual line bundle on the entire base. -/
theorem fppfSourceLineGlued_locallyFreeRankOne :
    LocallyFreeRankOne (fppfSourceLineGlued p D hM) := by
  let _ := fppfSourceCharts_quasicoherent p hM
  exact openGlued_locallyFreeRankOne D (fun y ↦ (fppfSourceCharts p y).chart)
    (fppfSourceCharts_baseCovers p) hM

/-- Reconstruction on each member of an actual open cover of the original source. -/
def fppfSourceLineRecoveryIso (y : Y) :
    (pullback (fppfSourceCharts p y).sourceMap).obj
        ((pullback p).obj (fppfSourceLineGlued p D hM)) ≅
      (pullback (fppfSourceCharts p y).sourceMap).obj M := by
  let _ := fppfSourceCharts_quasicoherent p hM
  exact sourceRecoveryIso (fppfSourceCharts p) D y

end FLT.Mazur.SchemeAffineDescent
