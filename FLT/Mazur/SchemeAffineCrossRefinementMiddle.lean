/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementRawRestriction

/-!
# Restriction compatibility of the middle cross-refinement comparison

Transport the raw affine square to the packaged geometric comparisons. Structural
heterogeneous congruence changes the implicit module presentations separately,
so the kernel need not unfold pullback constructions to compare their types.
The final compatibility theorem is an ordinary equality of morphisms.
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

omit hL' in
/-- Present the pulled-back original middle edge followed by the right comparison. -/
theorem restriction_lhs_heq :
    HEq
      ((pullback (Spec.map α)).map (ρ.middleComparison D).hom ≫
        (ρ.rightChart.comparison (ρ.restrict ψ α β v hψ).rightChart D
          (ρ.restrictRight ψ α β v hψ)).hom)
      ((pullback (Spec.map α)).map
        (D.chartCrossCoverIso ρ.ringMap p ρ.leftChart.base ρ.leftChart.cover ρ.rightChart.cover
          ρ.leftChart.square ρ.rightChart.square ρ.faithfullyFlat).hom ≫
        (D.chartRefinementIsoTo ρ.ringMap ψ α β v p ρ.leftChart.base ρ.rightChart.cover
          ρ.rightChart.square ρ.faithfullyFlat hψ (ρ.restrict ψ α β v hψ).leftChart.base
          (ρ.restrict ψ α β v hψ).rightChart.cover
          (ρ.restrictLeft ψ α β v hψ).base_over (ρ.restrictRight ψ α β v hψ).cover_over
          (ρ.restrict ψ α β v hψ).rightChart.square).hom) := by
  congr! (config := { closePre := false, closePost := false }) 4
  all_goals first
    | exact ρ.middleComparison_eq D
    | exact ρ.comparison_restrictRight_eq ψ α β v hψ D
    | rfl
    | (unfold middleComparison; rfl)

omit hR in
/-- Compare the two presentations without converting the ambient morphism type. -/
theorem restriction_rhs_heq :
    HEq
      ((ρ.leftChart.comparison (ρ.restrict ψ α β v hψ).leftChart D
          (ρ.restrictLeft ψ α β v hψ)).hom ≫
        ((ρ.restrict ψ α β v hψ).middleComparison D).hom)
      ((D.chartRefinementIsoTo ρ.ringMap ψ α β v p ρ.leftChart.base ρ.leftChart.cover
          ρ.leftChart.square ρ.faithfullyFlat hψ (ρ.restrict ψ α β v hψ).leftChart.base
          (ρ.restrict ψ α β v hψ).leftChart.cover
          (ρ.restrictLeft ψ α β v hψ).base_over (ρ.restrictLeft ψ α β v hψ).cover_over
          (ρ.restrict ψ α β v hψ).leftChart.square).hom ≫
        (D.chartCrossCoverIso ψ p (ρ.restrict ψ α β v hψ).leftChart.base
          (ρ.restrict ψ α β v hψ).leftChart.cover (ρ.restrict ψ α β v hψ).rightChart.cover
          (ρ.restrict ψ α β v hψ).leftChart.square
          (ρ.restrict ψ α β v hψ).rightChart.square hψ).hom) := by
  congr! (config := { closePre := false, closePost := false }) 4
  all_goals first
    | exact ρ.middleComparison_restrict_eq ψ α β v hψ D
    | exact ρ.comparison_restrictLeft_eq ψ α β v hψ D
    | rfl
    | (unfold middleComparison; rfl)

/-- Restriction preserves the middle comparison for the independent covering maps. -/
theorem middleComparison_restrict :
    (pullback (Spec.map α)).map (ρ.middleComparison D).hom ≫
        (ρ.rightChart.comparison (ρ.restrict ψ α β v hψ).rightChart D
          (ρ.restrictRight ψ α β v hψ)).hom =
      (ρ.leftChart.comparison (ρ.restrict ψ α β v hψ).leftChart D
          (ρ.restrictLeft ψ α β v hψ)).hom ≫
        ((ρ.restrict ψ α β v hψ).middleComparison D).hom := by
  exact eq_of_heq ((ρ.restriction_lhs_heq ψ α β v hψ D).trans
    ((heq_of_eq (ρ.restricted_raw_square ψ α β v hψ D)).trans
      (ρ.restriction_rhs_heq ψ α β v hψ D).symm))

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
