/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineBaseRecoveryCharts
public import FLT.Mazur.SchemeCanonicalChartRecognition
public import FLT.Mazur.SchemeFppfSourceLineGluing

/-!
# Local base-object round trips for fppf line-bundle descent

Every base line bundle is recovered from its canonical pullback datum on each
member of the constructed affine base cover. Overlap compatibility is separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open FCurve SchemeGeometricDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
variable (A : X.Modules) (hA : LocallyFreeRankOne A)

include hA in
/-- The restricted base line bundle is quasi-coherent on each constructed base chart. -/
lemma fppfBaseLineCharts_quasicoherent (y : Y) :
    ((pullback (fppfSourceCharts p y).chart.base).obj A).IsQuasicoherent := by
  let _ := SchemePicard.rankOne_finitePresentation _
    (hA.pullback (fppfSourceCharts p y).chart.base)
  infer_instance

/-- The base-object round trip is an isomorphism on every original affine base chart. -/
def fppfLineBaseChartIso (y : Y) :
    (pullback (fppfSourceCharts p y).chart.base).obj A ≅
      (pullback (fppfSourceCharts p y).chart.base).obj
        (fppfSourceLineGlued p (canonical p A) (hA.pullback p)) := by
  let _ := fppfBaseLineCharts_quasicoherent p A hA
  let _ := fppfSourceCharts_quasicoherent p (hA.pullback p)
  exact baseRecoveryChartIso (fun y ↦ (fppfSourceCharts p y).chart)
    (canonical p A) A (Iso.refl _) (canonical_overlap_chart p A) y

end FLT.Mazur.SchemeAffineDescent
