/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementComparison

/-!
# Quasicoherence on independently chosen common covers

Each branch is an affine pullback of its original covering chart. Quasicoherence
therefore follows from the original chart, including for canonical common covers
and further base changes. No relation between the two covering maps is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p}
variable (ρ : C.CrossRefinement C') {M : Y.Modules}

/-- The first common-cover branch inherits quasicoherence from its original chart. -/
instance leftChart_isQuasicoherent [((pullback C.cover).obj M).IsQuasicoherent] :
    ((pullback ρ.leftChart.cover).obj M).IsQuasicoherent :=
  SchemeGeometricDescent.Data.isQuasicoherent_compositeChartPullback ρ.leftCover C.cover

/-- The second branch inherits quasicoherence through its independent covering map. -/
instance rightChart_isQuasicoherent [((pullback C'.cover).obj M).IsQuasicoherent] :
    ((pullback ρ.rightChart.cover).obj M).IsQuasicoherent :=
  SchemeGeometricDescent.Data.isQuasicoherent_compositeChartPullback ρ.rightCover C'.cover

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
