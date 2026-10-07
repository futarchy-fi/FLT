/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementPresentation

/-!
# Restriction squares in explicit affine presentations

Name the geometric comparisons in the explicit affine sheaf presentations.
Their restriction square follows from the ring refinement recognition theorem;
the separate maps into the original covering scheme remain in every edge.
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

/-- The middle comparison with the ambient module category fixed explicitly. -/
def sourceMiddleRingIso : @Iso (Spec ρ.baseRing).Modules _
    (D.chartSheaf ρ.ringMap p ρ.leftChart.base ρ.leftChart.cover
      ρ.leftChart.square ρ.faithfullyFlat)
    (D.chartSheaf ρ.ringMap p ρ.leftChart.base ρ.rightChart.cover
      ρ.rightChart.square ρ.faithfullyFlat) := ρ.middleComparison D

omit hL hR in
/-- The restricted middle comparison in the module category of the new base. -/
def targetMiddleRingIso : @Iso (Spec A).Modules _
    (D.chartSheaf ψ p (ρ.restrict ψ α β v hψ).leftChart.base
      (ρ.restrict ψ α β v hψ).leftChart.cover
      (ρ.restrict ψ α β v hψ).leftChart.square hψ)
    (D.chartSheaf ψ p (ρ.restrict ψ α β v hψ).leftChart.base
      (ρ.restrict ψ α β v hψ).rightChart.cover
      (ρ.restrict ψ α β v hψ).rightChart.square hψ) :=
  (ρ.restrict ψ α β v hψ).middleComparison D

omit hR hR' in
/-- The left branch comparison with its base pullback expressed by the ring map. -/
def restrictionLeftRingIso : @Iso (Spec A).Modules _
    ((pullback (Spec.map α)).obj (D.chartSheaf ρ.ringMap p ρ.leftChart.base ρ.leftChart.cover
      ρ.leftChart.square ρ.faithfullyFlat))
    (D.chartSheaf ψ p (ρ.restrict ψ α β v hψ).leftChart.base
      (ρ.restrict ψ α β v hψ).leftChart.cover
      (ρ.restrict ψ α β v hψ).leftChart.square hψ) :=
  ρ.leftChart.comparison _ D (ρ.restrictLeft ψ α β v hψ)

omit hL hL' in
/-- The right branch comparison retains the independent covering map. -/
def restrictionRightRingIso : @Iso (Spec A).Modules _
    ((pullback (Spec.map α)).obj (D.chartSheaf ρ.ringMap p ρ.leftChart.base ρ.rightChart.cover
      ρ.rightChart.square ρ.faithfullyFlat))
    (D.chartSheaf ψ p (ρ.restrict ψ α β v hψ).leftChart.base
      (ρ.restrict ψ α β v hψ).rightChart.cover
      (ρ.restrict ψ α β v hψ).rightChart.square hψ) :=
  ρ.rightChart.comparison _ D (ρ.restrictRight ψ α β v hψ)

attribute [local irreducible] sourceMiddleRingIso targetMiddleRingIso
attribute [local irreducible] restrictionLeftRingIso restrictionRightRingIso

/-- The geometric comparisons commute in their explicit affine presentations. -/
theorem ringMiddleComparison_restrict :
    (pullback (Spec.map α)).map (ρ.sourceMiddleRingIso D).hom ≫
        (ρ.restrictionRightRingIso ψ α β v hψ D).hom =
      (ρ.restrictionLeftRingIso ψ α β v hψ D).hom ≫
        (ρ.targetMiddleRingIso ψ α β v hψ D).hom := by
  apply SchemeGeometricDescent.Data.chartCrossCoverIso_refinement_of_eq
    ρ.ringMap ψ α β v p D ρ.leftChart.base ρ.leftChart.cover ρ.rightChart.cover
    ρ.leftChart.square ρ.rightChart.square ρ.faithfullyFlat hψ
    (ρ.restrict ψ α β v hψ).leftChart.base
    (ρ.restrict ψ α β v hψ).leftChart.cover (ρ.restrict ψ α β v hψ).rightChart.cover
    (ρ.restrictLeft ψ α β v hψ).base_over (ρ.restrictLeft ψ α β v hψ).cover_over
    (ρ.restrictRight ψ α β v hψ).cover_over
    (ρ.restrict ψ α β v hψ).leftChart.square (ρ.restrict ψ α β v hψ).rightChart.square
  · unfold sourceMiddleRingIso
    exact ρ.middleComparison_eq D
  · unfold targetMiddleRingIso
    exact ρ.middleComparison_restrict_eq ψ α β v hψ D
  · unfold restrictionLeftRingIso
    exact ρ.comparison_restrictLeft_eq ψ α β v hψ D
  · unfold restrictionRightRingIso
    exact ρ.comparison_restrictRight_eq ψ α β v hψ D

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
