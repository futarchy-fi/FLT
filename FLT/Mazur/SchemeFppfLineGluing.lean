/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCoverRecovery
public import FLT.Mazur.SchemeAffineFppfChartCover
public import FLT.Mazur.SchemeAffineOpenGluingLine

/-!
# Gluing a line bundle from actual fppf descent charts

For an fppf morphism, construct the affine chart family and all local
quasi-coherence instances from the original line bundle. The resulting
glued sheaf is a line bundle and reconstructs the original object on each
constructed covering chart. Global reconstruction is a separate step.
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
/-- The original line bundle supplies every affine chart's quasi-coherence instance. -/
lemma fppfCharts_quasicoherent (i : X.affineOpenCover.I₀) :
    ((pullback (fppfCharts p i).cover).obj M).IsQuasicoherent := by
  let _ := SchemePicard.rankOne_finitePresentation _ (hM.pullback (fppfCharts p i).cover)
  infer_instance

/-- The actual line-bundle candidate obtained from fppf geometric descent data. -/
def fppfLineGlued : X.Modules := by
  let _ := fppfCharts_quasicoherent p hM
  exact openGlued (fppfCharts p) D

/-- The constructed global sheaf is locally free of rank one. -/
theorem fppfLineGlued_locallyFreeRankOne : LocallyFreeRankOne (fppfLineGlued p D hM) := by
  let _ := fppfCharts_quasicoherent p hM
  exact openGlued_locallyFreeRankOne D (fppfCharts p) (fppfCharts_covers p) hM

/-- The constructed sheaf restricts to effective descent on each original base chart. -/
def fppfLineGluedChartIso (i : X.affineOpenCover.I₀) :
    (pullback (fppfCharts p i).base).obj (fppfLineGlued p D hM) ≅
      @Chart.sheaf _ _ p (fppfCharts p i) M D (fppfCharts_quasicoherent p hM i) := by
  let _ := fppfCharts_quasicoherent p hM
  exact openGluedChartIso (fppfCharts p) D i

/-- The original line bundle is reconstructed on each constructed covering chart. -/
def fppfLineCoverRecoveryIso (i : X.affineOpenCover.I₀) :
    (pullback (fppfCharts p i).cover).obj ((pullback p).obj (fppfLineGlued p D hM)) ≅
      (pullback (fppfCharts p i).cover).obj M := by
  let _ := fppfCharts_quasicoherent p hM
  exact coverRecoveryIso (fppfCharts p) D i

end FLT.Mazur.SchemeAffineDescent
