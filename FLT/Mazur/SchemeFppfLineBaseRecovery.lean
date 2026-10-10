/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineBaseRecovery
public import FLT.Mazur.SchemeFppfLineBaseRecoveryCharts
public import FLT.Mazur.SchemeFppfLineGluingFunctor
public import FLT.Mazur.SchemeLineCanonicalFunctor

/-!
# The global base-object round trip for fppf line descent

The constructed affine base cover glues the local recognition isomorphisms.
This gives an actual isomorphism from each base line bundle to the gluing
of its canonical descent datum.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open FCurve SchemeGeometricDescent SchemePicard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]
/-- The constructed affine base charts are jointly surjective on points. -/
lemma fppfSourceCharts_baseCover_range (x : X) :
    ∃ y, x ∈ Set.range (fppfSourceCharts p y).chart.base := by
  have h : x ∈ ⨆ y, (fppfSourceCharts p y).chart.base.opensRange := by
    rw [fppfSourceCharts_baseCovers]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.mp h

variable (A : X.Modules) (hA : LocallyFreeRankOne A)

/-- Every base line bundle is globally recovered from its canonical descent datum. -/
def fppfLineBaseRecoveryIso :
    A ≅ fppfSourceLineGlued p (canonical p A) (hA.pullback p) := by
  let _ := fppfBaseLineCharts_quasicoherent p A hA
  let _ := fppfSourceCharts_quasicoherent p (hA.pullback p)
  exact baseRecoveryIso (fun y ↦ (fppfSourceCharts p y).chart)
    (canonical p A) A (Iso.refl _) (canonical_overlap_chart p A)
    (fppfSourceCharts_baseCover_range p)

/-- The global round trip retains its original affine base-chart maps. -/
lemma fppfLineBaseRecoveryIso_chart (y : Y) :
    (pullback (fppfSourceCharts p y).chart.base).map
        (fppfLineBaseRecoveryIso p A hA).hom = (fppfLineBaseChartIso p A hA y).hom := by
  let _ := fppfBaseLineCharts_quasicoherent p A hA
  let _ := fppfSourceCharts_quasicoherent p (hA.pullback p)
  exact baseRecoveryIso_chart (fun y ↦ (fppfSourceCharts p y).chart)
    (canonical p A) A (Iso.refl _) (canonical_overlap_chart p A)
    (fppfSourceCharts_baseCover_range p) y

/-- The base-object round trip in the category of actual line bundles. -/
def lineBaseRecoveryIso (L : LineBundleCat X) :
    L ≅ (lineGluing p).obj ((lineCanonical p).obj L) :=
  InducedCategory.isoMk (fppfLineBaseRecoveryIso p L.1 L.2)

end FLT.Mazur.SchemeAffineDescent
