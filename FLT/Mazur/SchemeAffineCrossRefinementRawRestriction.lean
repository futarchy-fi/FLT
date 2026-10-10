/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossCoverRefinement
public import FLT.Mazur.SchemeAffineCrossRefinementComparison
public import FLT.Mazur.SchemeAffineCrossRefinementPresentation

/-!
# Raw comparison squares on restricted cross refinements

Specialize the effective ring refinement theorem to both geometric branches.
The explicit affine sheaf presentations keep this kernel check small.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p} (ρ : C.CrossRefinement C')
variable {A B : CommRingCat.{u}} (ψ : A ⟶ B)
variable (α : ρ.baseRing ⟶ A) (β : ρ.coverRing ⟶ B)
variable (v : ρ.ringMap ≫ β = α ≫ ψ) (hψ : ψ.hom.FaithfullyFlat)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [hL : ((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
variable [hR : ((pullback ρ.rightChart.cover).obj M).IsQuasicoherent]
variable [hL' : ((pullback (ρ.restrict ψ α β v hψ).leftChart.cover).obj M).IsQuasicoherent]
variable [hR' : ((pullback (ρ.restrict ψ α β v hψ).rightChart.cover).obj M).IsQuasicoherent]

attribute [local irreducible] middleComparison Chart.comparison
attribute [local irreducible] SchemeGeometricDescent.Data.chartSheaf
attribute [local irreducible] SchemeGeometricDescent.Data.chartCrossCoverIso
attribute [local irreducible] SchemeGeometricDescent.Data.chartRefinementIsoTo

/-- The raw comparison square specialized to the two branches of a cross refinement. -/
theorem restricted_raw_square :
    (pullback (Spec.map α)).map
      (D.chartCrossCoverIso ρ.ringMap p ρ.leftChart.base ρ.leftChart.cover ρ.rightChart.cover
      ρ.leftChart.square ρ.rightChart.square ρ.faithfullyFlat).hom ≫
      (D.chartRefinementIsoTo ρ.ringMap ψ α β v p ρ.leftChart.base ρ.rightChart.cover
      ρ.rightChart.square ρ.faithfullyFlat hψ (ρ.restrict ψ α β v hψ).leftChart.base
      (ρ.restrict ψ α β v hψ).rightChart.cover
      (ρ.restrictLeft ψ α β v hψ).base_over (ρ.restrictRight ψ α β v hψ).cover_over
      (ρ.restrict ψ α β v hψ).rightChart.square).hom =
      (D.chartRefinementIsoTo ρ.ringMap ψ α β v p ρ.leftChart.base ρ.leftChart.cover
      ρ.leftChart.square ρ.faithfullyFlat hψ (ρ.restrict ψ α β v hψ).leftChart.base
      (ρ.restrict ψ α β v hψ).leftChart.cover
      (ρ.restrictLeft ψ α β v hψ).base_over (ρ.restrictLeft ψ α β v hψ).cover_over
      (ρ.restrict ψ α β v hψ).leftChart.square).hom ≫
      (D.chartCrossCoverIso ψ p (ρ.restrict ψ α β v hψ).leftChart.base
      (ρ.restrict ψ α β v hψ).leftChart.cover (ρ.restrict ψ α β v hψ).rightChart.cover
      (ρ.restrict ψ α β v hψ).leftChart.square
      (ρ.restrict ψ α β v hψ).rightChart.square hψ).hom := by
  exact @SchemeGeometricDescent.Data.chartCrossCoverIso_refinement
    ρ.baseRing ρ.coverRing A B ρ.ringMap ψ α β v X Y p M D ρ.leftChart.base
    ρ.leftChart.cover ρ.rightChart.cover ρ.leftChart.square ρ.rightChart.square
    ρ.faithfullyFlat hψ (ρ.restrict ψ α β v hψ).leftChart.base
    (ρ.restrict ψ α β v hψ).leftChart.cover (ρ.restrict ψ α β v hψ).rightChart.cover
    (ρ.restrictLeft ψ α β v hψ).base_over (ρ.restrictLeft ψ α β v hψ).cover_over
    (ρ.restrictRight ψ α β v hψ).cover_over
    (ρ.restrict ψ α β v hψ).leftChart.square (ρ.restrict ψ α β v hψ).rightChart.square
    hL hR hL' hR'

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
