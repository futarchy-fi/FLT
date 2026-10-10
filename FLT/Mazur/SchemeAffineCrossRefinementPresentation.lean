/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossCoverRefinementRecognition
public import FLT.Mazur.SchemeAffineCrossRefinementComparison
public import FLT.Mazur.SchemeAffineCrossRefinementRestriction

/-!
# Restriction compatibility of the middle cross-refinement comparison

The geometric restriction refines each branch separately. The middle effective
comparison intertwines these two branch comparisons by faithful reconstruction.
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
variable [((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback ρ.rightChart.cover).obj M).IsQuasicoherent]
variable [((pullback (ρ.restrict ψ α β v hψ).leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback (ρ.restrict ψ α β v hψ).rightChart.cover).obj M).IsQuasicoherent]

attribute [local irreducible] middleComparison Chart.comparison
attribute [local irreducible] SchemeGeometricDescent.Data.chartSheaf
attribute [local irreducible] SchemeGeometricDescent.Data.chartCrossCoverIso
attribute [local irreducible] SchemeGeometricDescent.Data.chartRefinementIsoTo

/-- The original middle comparison has the expected ring presentation. -/
theorem middleComparison_eq :
    ρ.middleComparison D =
      D.chartCrossCoverIso ρ.ringMap p ρ.leftChart.base ρ.leftChart.cover ρ.rightChart.cover
        ρ.leftChart.square ρ.rightChart.square ρ.faithfullyFlat := by
  unfold middleComparison
  rfl

omit [((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
  [((pullback ρ.rightChart.cover).obj M).IsQuasicoherent] in
/-- The restricted middle comparison has the new covering ring as its presentation. -/
theorem middleComparison_restrict_eq :
    (ρ.restrict ψ α β v hψ).middleComparison D =
      D.chartCrossCoverIso ψ p (ρ.restrict ψ α β v hψ).leftChart.base
        (ρ.restrict ψ α β v hψ).leftChart.cover (ρ.restrict ψ α β v hψ).rightChart.cover
        (ρ.restrict ψ α β v hψ).leftChart.square (ρ.restrict ψ α β v hψ).rightChart.square
        hψ := by
  unfold middleComparison
  rfl

omit [((pullback ρ.rightChart.cover).obj M).IsQuasicoherent]
  [((pullback (ρ.restrict ψ α β v hψ).rightChart.cover).obj M).IsQuasicoherent] in
/-- The first restricted branch comparison has the expected ring presentation. -/
theorem comparison_restrictLeft_eq :
    ρ.leftChart.comparison (ρ.restrict ψ α β v hψ).leftChart D
        (ρ.restrictLeft ψ α β v hψ) =
      D.chartRefinementIsoTo ρ.ringMap ψ α β v p ρ.leftChart.base ρ.leftChart.cover
        ρ.leftChart.square ρ.faithfullyFlat hψ (ρ.restrict ψ α β v hψ).leftChart.base
        (ρ.restrict ψ α β v hψ).leftChart.cover
        (ρ.restrictLeft ψ α β v hψ).base_over (ρ.restrictLeft ψ α β v hψ).cover_over
        (ρ.restrict ψ α β v hψ).leftChart.square := by
  unfold Chart.comparison
  rfl

omit [((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
  [((pullback (ρ.restrict ψ α β v hψ).leftChart.cover).obj M).IsQuasicoherent] in
/-- The second branch keeps its independent covering map in the ring presentation. -/
theorem comparison_restrictRight_eq :
    ρ.rightChart.comparison (ρ.restrict ψ α β v hψ).rightChart D
        (ρ.restrictRight ψ α β v hψ) =
      D.chartRefinementIsoTo ρ.ringMap ψ α β v p ρ.leftChart.base ρ.rightChart.cover
        ρ.rightChart.square ρ.faithfullyFlat hψ (ρ.restrict ψ α β v hψ).leftChart.base
        (ρ.restrict ψ α β v hψ).rightChart.cover
        (ρ.restrictLeft ψ α β v hψ).base_over (ρ.restrictRight ψ α β v hψ).cover_over
        (ρ.restrict ψ α β v hψ).rightChart.square := by
  unfold Chart.comparison
  rfl


end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
