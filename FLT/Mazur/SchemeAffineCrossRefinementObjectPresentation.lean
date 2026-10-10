/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementPresentation
public import FLT.Mazur.SchemeAffineCrossRefinementComparison
public import FLT.Mazur.SchemeAffineCrossRefinementRestriction

/-!
# Object isomorphisms for cross-refinement presentations

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

/-- The first original chart sheaf and its explicit affine presentation. -/
def sourceLeftPresentation : ρ.leftChart.sheaf D ≅
    D.chartSheaf ρ.ringMap p ρ.leftChart.base ρ.leftChart.cover
      ρ.leftChart.square ρ.faithfullyFlat := Iso.refl _

/-- The second original chart retains its own covering map in its affine presentation. -/
def sourceRightPresentation : ρ.rightChart.sheaf D ≅
    D.chartSheaf ρ.ringMap p ρ.leftChart.base ρ.rightChart.cover
      ρ.rightChart.square ρ.faithfullyFlat := Iso.refl _

/-- The first restricted chart sheaf presented over the new base ring. -/
def targetLeftPresentation : (ρ.restrict ψ α β v hψ).leftChart.sheaf D ≅
    D.chartSheaf ψ p (ρ.restrict ψ α β v hψ).leftChart.base
      (ρ.restrict ψ α β v hψ).leftChart.cover
      (ρ.restrict ψ α β v hψ).leftChart.square hψ := Iso.refl _

/-- The second restricted chart sheaf with its independent covering map. -/
def targetRightPresentation : (ρ.restrict ψ α β v hψ).rightChart.sheaf D ≅
    D.chartSheaf ψ p (ρ.restrict ψ α β v hψ).leftChart.base
      (ρ.restrict ψ α β v hψ).rightChart.cover
      (ρ.restrict ψ α β v hψ).rightChart.square hψ := Iso.refl _

attribute [local irreducible] middleComparison Chart.comparison
attribute [local irreducible] SchemeGeometricDescent.Data.chartSheaf
attribute [local irreducible] SchemeGeometricDescent.Data.chartCrossCoverIso
attribute [local irreducible] SchemeGeometricDescent.Data.chartRefinementIsoTo

/-- Presenting the original middle edge preserves its comparison. -/
theorem middleComparison_presentation :
    ρ.middleComparison D ≪≫ ρ.sourceRightPresentation D =
      ρ.sourceLeftPresentation D ≪≫
        D.chartCrossCoverIso ρ.ringMap p ρ.leftChart.base ρ.leftChart.cover ρ.rightChart.cover
          ρ.leftChart.square ρ.rightChart.square ρ.faithfullyFlat := by
  simpa only [sourceLeftPresentation, sourceRightPresentation, Iso.trans_refl, Iso.refl_trans]
    using ρ.middleComparison_eq D

omit [((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
  [((pullback ρ.rightChart.cover).obj M).IsQuasicoherent] in
/-- Presenting the restricted middle edge preserves its comparison. -/
theorem middleComparison_restrict_presentation :
    (ρ.restrict ψ α β v hψ).middleComparison D ≪≫
        ρ.targetRightPresentation ψ α β v hψ D =
      ρ.targetLeftPresentation ψ α β v hψ D ≪≫
        D.chartCrossCoverIso ψ p (ρ.restrict ψ α β v hψ).leftChart.base
          (ρ.restrict ψ α β v hψ).leftChart.cover (ρ.restrict ψ α β v hψ).rightChart.cover
          (ρ.restrict ψ α β v hψ).leftChart.square
          (ρ.restrict ψ α β v hψ).rightChart.square hψ := by
  simpa only [targetLeftPresentation, targetRightPresentation, Iso.trans_refl, Iso.refl_trans]
    using ρ.middleComparison_restrict_eq ψ α β v hψ D

omit [((pullback ρ.rightChart.cover).obj M).IsQuasicoherent]
  [((pullback (ρ.restrict ψ α β v hψ).rightChart.cover).obj M).IsQuasicoherent] in
/-- Presenting the first vertical comparison commutes with base pullback. -/
theorem comparison_restrictLeft_presentation :
    ρ.leftChart.comparison (ρ.restrict ψ α β v hψ).leftChart D
        (ρ.restrictLeft ψ α β v hψ) ≪≫ ρ.targetLeftPresentation ψ α β v hψ D =
      (pullback (Spec.map α)).mapIso (ρ.sourceLeftPresentation D) ≪≫
        D.chartRefinementIsoTo ρ.ringMap ψ α β v p ρ.leftChart.base ρ.leftChart.cover
          ρ.leftChart.square ρ.faithfullyFlat hψ (ρ.restrict ψ α β v hψ).leftChart.base
          (ρ.restrict ψ α β v hψ).leftChart.cover
          (ρ.restrictLeft ψ α β v hψ).base_over (ρ.restrictLeft ψ α β v hψ).cover_over
          (ρ.restrict ψ α β v hψ).leftChart.square := by
  simpa only [sourceLeftPresentation, targetLeftPresentation, Functor.mapIso_refl,
    Iso.trans_refl, Iso.refl_trans] using ρ.comparison_restrictLeft_eq ψ α β v hψ D

omit [((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
  [((pullback (ρ.restrict ψ α β v hψ).leftChart.cover).obj M).IsQuasicoherent] in
/-- Presenting the second vertical comparison preserves its separate covering map. -/
theorem comparison_restrictRight_presentation :
    ρ.rightChart.comparison (ρ.restrict ψ α β v hψ).rightChart D
        (ρ.restrictRight ψ α β v hψ) ≪≫ ρ.targetRightPresentation ψ α β v hψ D =
      (pullback (Spec.map α)).mapIso (ρ.sourceRightPresentation D) ≪≫
        D.chartRefinementIsoTo ρ.ringMap ψ α β v p ρ.leftChart.base ρ.rightChart.cover
          ρ.rightChart.square ρ.faithfullyFlat hψ (ρ.restrict ψ α β v hψ).leftChart.base
          (ρ.restrict ψ α β v hψ).rightChart.cover
          (ρ.restrictLeft ψ α β v hψ).base_over (ρ.restrictRight ψ α β v hψ).cover_over
          (ρ.restrict ψ α β v hψ).rightChart.square := by
  simpa only [sourceRightPresentation, targetRightPresentation, Functor.mapIso_refl,
    Iso.trans_refl, Iso.refl_trans] using ρ.comparison_restrictRight_eq ψ α β v hψ D

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
