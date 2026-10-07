/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementRestriction
public import FLT.Mazur.SchemeAffineChartComparisonComposition

/-!
# Restriction of the two outer comparison edges

Specialize composition of geometric chart comparisons to the two branches of
a restricted cross refinement. Each branch retains its own covering map.
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
attribute [local irreducible] Chart.comparison

section Left
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback (ρ.restrict ψ α β v hψ).leftChart.cover).obj M).IsQuasicoherent]

/-- Restricting the first outer chart comparison composes its actual refinements. -/
theorem leftComparison_restrict :
    (pullback (Spec.map α)).map (C.comparison ρ.leftChart D ρ.leftRefinement).hom ≫
        (ρ.leftChart.comparison (ρ.restrict ψ α β v hψ).leftChart D
          (ρ.restrictLeft ψ α β v hψ)).hom =
      (AffineRefinementPullback.compositionChart ρ.leftBase α (C.sheaf D)).hom ≫
        (C.comparison (ρ.restrict ψ α β v hψ).leftChart D
          (ρ.restrict ψ α β v hψ).leftRefinement).hom := by
  have h := C.comparison_composition ρ.leftChart
    (ρ.restrict ψ α β v hψ).leftChart D ρ.leftRefinement
    (ρ.restrictLeft ψ α β v hψ)
  have hl : HEq
      ((pullback (Spec.map α)).map (C.comparison ρ.leftChart D ρ.leftRefinement).hom ≫
        (ρ.leftChart.comparison (ρ.restrict ψ α β v hψ).leftChart D
          (ρ.restrictLeft ψ α β v hψ)).hom)
      ((pullback (Spec.map (ρ.restrictLeft ψ α β v hψ).base)).map
          (C.comparison ρ.leftChart D ρ.leftRefinement).hom ≫
        (ρ.leftChart.comparison (ρ.restrict ψ α β v hψ).leftChart D
          (ρ.restrictLeft ψ α β v hψ)).hom) := by
    congr! (config := { closePre := false, closePost := false }) 4 <;> rfl
  have hr : HEq
      ((AffineRefinementPullback.compositionChart ρ.leftBase α (C.sheaf D)).hom ≫
        (C.comparison (ρ.restrict ψ α β v hψ).leftChart D
          (ρ.restrict ψ α β v hψ).leftRefinement).hom)
      ((C.compositionPullback ρ.leftChart (ρ.restrict ψ α β v hψ).leftChart D
          ρ.leftRefinement (ρ.restrictLeft ψ α β v hψ)).hom ≫
        (C.comparison (ρ.restrict ψ α β v hψ).leftChart D
          (ρ.leftRefinement.comp (ρ.restrictLeft ψ α β v hψ))).hom) := by
    congr! (config := { closePre := false, closePost := false }) 4 <;> rfl
  exact eq_of_heq (hl.trans ((heq_of_eq h).trans hr.symm))

end Left

section Right
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable [((pullback ρ.rightChart.cover).obj M).IsQuasicoherent]
variable [((pullback (ρ.restrict ψ α β v hψ).rightChart.cover).obj M).IsQuasicoherent]

/-- Restricting the second outer comparison preserves its separate covering map. -/
theorem rightComparison_restrict :
    (pullback (Spec.map α)).map (C'.comparison ρ.rightChart D ρ.rightRefinement).hom ≫
        (ρ.rightChart.comparison (ρ.restrict ψ α β v hψ).rightChart D
          (ρ.restrictRight ψ α β v hψ)).hom =
      (AffineRefinementPullback.compositionChart ρ.rightBase α (C'.sheaf D)).hom ≫
        (C'.comparison (ρ.restrict ψ α β v hψ).rightChart D
          (ρ.restrict ψ α β v hψ).rightRefinement).hom := by
  have h := C'.comparison_composition ρ.rightChart
    (ρ.restrict ψ α β v hψ).rightChart D ρ.rightRefinement
    (ρ.restrictRight ψ α β v hψ)
  have hl : HEq
      ((pullback (Spec.map α)).map (C'.comparison ρ.rightChart D ρ.rightRefinement).hom ≫
        (ρ.rightChart.comparison (ρ.restrict ψ α β v hψ).rightChart D
          (ρ.restrictRight ψ α β v hψ)).hom)
      ((pullback (Spec.map (ρ.restrictRight ψ α β v hψ).base)).map
          (C'.comparison ρ.rightChart D ρ.rightRefinement).hom ≫
        (ρ.rightChart.comparison (ρ.restrict ψ α β v hψ).rightChart D
          (ρ.restrictRight ψ α β v hψ)).hom) := by
    congr! (config := { closePre := false, closePost := false }) 4 <;> rfl
  have hr : HEq
      ((AffineRefinementPullback.compositionChart ρ.rightBase α (C'.sheaf D)).hom ≫
        (C'.comparison (ρ.restrict ψ α β v hψ).rightChart D
          (ρ.restrict ψ α β v hψ).rightRefinement).hom)
      ((C'.compositionPullback ρ.rightChart (ρ.restrict ψ α β v hψ).rightChart D
          ρ.rightRefinement (ρ.restrictRight ψ α β v hψ)).hom ≫
        (C'.comparison (ρ.restrict ψ α β v hψ).rightChart D
          (ρ.rightRefinement.comp (ρ.restrictRight ψ α β v hψ))).hom) := by
    congr! (config := { closePre := false, closePost := false }) 4 <;> rfl
  exact eq_of_heq (hl.trans ((heq_of_eq h).trans hr.symm))

end Right
end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
