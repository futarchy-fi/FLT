/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveReesSchemeOverlap
public import FLT.Mazur.BlowupReesRatioTransition

/-!
# The successive equation transition commutes in Rees Proj

The actual substitution preserves every preceding divided function, hence
is the canonical transition on the full intersection of the Rees charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BX" => WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "I" => WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6
local notation "ref" => WeierstrassDilatation.refinement W s π
  (π * b3) (π * b4) (π ^ 2 * b6) b3 b4 b6 rfl rfl rfl

/-- The original scale fraction chart included in the common Rees Proj. -/
def scaleProjInclusion :
    Spec (.of (WeierstrassSuccessiveScale.scaleReesChart W s π b3 b4 b6)) ⟶
      BlowupRees.proj I :=
  BlowupRees.fractionChartInclusion I (algebraMap R B π) (Ideal.subset_span (by simp))

/-- The original horizontal fraction chart included in the common Rees Proj. -/
def horizontalProjInclusion :
    Spec (.of (WeierstrassSuccessiveX.horizontalReesChart W s π b3 b4 b6)) ⟶
      BlowupRees.proj I :=
  BlowupRees.fractionChartInclusion I BX (Ideal.subset_span (by simp))

/-- Preceding functions in the scale fraction chart. -/
def scaleOriginalMap : B →+* WeierstrassSuccessiveScale.scaleReesChart W s π b3 b4 b6 :=
  algebraMap B (BlowupFractionChart.chart I (algebraMap R B π))

/-- Preceding functions in the horizontal fraction chart. -/
def horizontalOriginalMap : B →+* WeierstrassSuccessiveX.horizontalReesChart W s π b3 b4 b6 :=
  algebraMap B (BlowupFractionChart.chart I BX)

variable [IsDomain R] (hπ : π ≠ 0)

/-- The actual fraction transition preserves every function on the preceding divided chart. -/
theorem scaleHorizontalTransition_original (z : B) :
    scaleHorizontalTransition W s π b3 b4 b6 hπ
      (BlowupRees.originalOnRatio I (algebraMap R B π) BX
        (Ideal.subset_span (by simp)) z) =
      BlowupRees.originalOnRatio I BX (algebraMap R B π)
        (Ideal.subset_span (by simp)) z := by
  have hs0 : WeierstrassSuccessiveScale.scaleReesChartEquiv W s π b3 b4 b6
      (IsRegular.of_ne_zero hπ) (ref z) =
        scaleOriginalMap W s π b3 b4 b6 z :=
    Subtype.ext (WeierstrassSuccessiveScale.scaleReesChartEquiv_refinement
      W s π b3 b4 b6 (IsRegular.of_ne_zero hπ) z)
  have hx0 : WeierstrassSuccessiveX.horizontalReesChartEquiv W s π b3 b4 b6 hπ
      (WeierstrassSuccessiveX.fromDivided W s π b3 b4 b6 z) =
        horizontalOriginalMap W s π b3 b4 b6 z :=
    Subtype.ext (WeierstrassSuccessiveX.horizontalReesChartEquiv_fromDivided
      W s π b3 b4 b6 hπ z)
  change scaleHorizontalTransition W s π b3 b4 b6 hπ
    (algebraMap _ _ (scaleOriginalMap W s π b3 b4 b6 z)) =
      algebraMap _ _ (horizontalOriginalMap W s π b3 b4 b6 z)
  rw [← hs0, scaleHorizontalTransition_base, ← hx0, ← horizontalScaleOpenEquiv_base]
  congr 1
  exact AlgHom.congr_fun
    (WeierstrassSuccessiveX.dividedToXOpen_refinement W s π b3 b4 b6) z

/-- The actual equation substitution commutes on the full Rees intersection. -/
@[reassoc] theorem horizontalOverlap_toProj :
    horizontalOverlapToScale W s π b3 b4 b6 hπ ≫ scaleProjInclusion W s π b3 b4 b6 =
      horizontalOpenInclusion W s π b3 b4 b6 ≫ horizontalProjInclusion W s π b3 b4 b6 := by
  rw [horizontalOverlapToScale_def, fractionOverlapIso_def, Category.assoc]
  exact BlowupRees.originalPreservingTransition_inclusion I (algebraMap R B π)
    (Ideal.subset_span (by simp)) BX (Ideal.subset_span (by simp))
    (scaleHorizontalTransition W s π b3 b4 b6 hπ).toRingHom
    (scaleHorizontalTransition_original W s π b3 b4 b6 hπ)

end FLT.Mazur.WeierstrassSuccessiveRees
