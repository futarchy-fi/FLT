/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesProjOverlap
public import FLT.Mazur.WeierstrassModificationReesYScaleScheme
public import FLT.Mazur.WeierstrassModificationYContractionOverlap

/-!
# The actual horizontal and vertical transitions commute in Rees Proj

The existing horizontal/vertical substitution retains all original cubic
functions and therefore agrees with the canonical full Rees transition.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s : R)

local notation "A" => WeierstrassIntegralChart.Coordinate W 2
local notation "I" => WeierstrassDilatation.modificationCenter W s
local notation "ox" => WeierstrassIntegralChart.coord W 2 0

local notation "oy" => WeierstrassIntegralChart.coord W 2 1

/-- The vertical fraction chart included in the same original Rees Proj. -/
def verticalProjInclusion :
    Spec (.of (WeierstrassModificationY.verticalReesChart W s)) ⟶ BlowupRees.proj I :=
  BlowupRees.fractionChartInclusion I oy (Ideal.subset_span (by simp))

variable [IsDomain R] [IsBezout R] (b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The existing horizontal/vertical transition preserves every original cubic function. -/
theorem horizontalVerticalTransition_original (z : A) :
    horizontalVerticalTransition W s b3 b4 b6 h3 h4 h6 hs
      (algebraMap _ (HorizontalVerticalOpen W s) (horizontalOriginalMap W s z)) =
        algebraMap _ (VerticalHorizontalOpen W s) (verticalOriginalMap W s z) := by
  have hx0 : WeierstrassModificationX.horizontalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs
      (WeierstrassModificationX.fromOriginal W s b3 b4 b6 h3 h4 h6 z) =
        horizontalOriginalMap W s z :=
    Subtype.ext (WeierstrassModificationX.horizontalReesChartEquiv_fromOriginal
      W s b3 b4 b6 h3 h4 h6 hs z)
  have hy0 : WeierstrassModificationY.verticalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs
      (WeierstrassModificationY.fromOriginal W s b3 b4 b6 h3 h4 h6 z) =
        verticalOriginalMap W s z :=
    Subtype.ext (WeierstrassModificationY.verticalReesChartEquiv_fromOriginal
      W s b3 b4 b6 h3 h4 h6 hs z)
  rw [← hx0, horizontalVerticalTransition_base, ← hy0, ← verticalHorizontalOpenEquiv_base]
  congr 1
  exact AlgHom.congr_fun (WeierstrassModificationY.toX_fromOriginal W s b3 b4 b6 h3 h4 h6
    (IsScalarTower.toAlgHom R _ (WeierstrassModificationY.HorizontalOpen W s b3 b4 b6))
    (WeierstrassModificationY.horizontalUnit W s b3 b4 b6)
    (WeierstrassModificationY.horizontalUnit_val W s b3 b4 b6).symm) z

/-- The actual vertical/horizontal substitution commutes on the full Proj overlap. -/
@[reassoc] theorem verticalHorizontal_toProj :
    verticalToHorizontal W s b3 b4 b6 h3 h4 h6 hs ≫ horizontalProjInclusion W s =
      verticalHorizontalInclusion W s ≫ verticalProjInclusion W s := by
  rw [verticalToHorizontal, verticalHorizontalTransitionIso_def, Category.assoc]
  exact BlowupRees.originalPreservingTransition_inclusion I ox
    (Ideal.subset_span (by simp)) oy (Ideal.subset_span (by simp))
    (horizontalVerticalTransition W s b3 b4 b6 h3 h4 h6 hs).toRingHom
    (horizontalVerticalTransition_original W s b3 b4 b6 h3 h4 h6 hs)

end FLT.Mazur.WeierstrassModificationReesCoordinates
