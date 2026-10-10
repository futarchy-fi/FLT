/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesProjYHorizontal

/-!
# The actual scale and vertical transitions commute in Rees Proj

The existing scale/vertical substitution retains all original cubic
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
local notation "oy" => WeierstrassIntegralChart.coord W 2 1

variable [IsDomain R] [IsBezout R] (b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The existing scale/vertical transition preserves every original cubic function. -/
theorem scaleVerticalTransition_original (z : A) :
    scaleVerticalTransition W s b3 b4 b6 h3 h4 h6 hs
      (algebraMap _ (ScaleVerticalOpen W s) (scaleOriginalMap W s z)) =
        algebraMap _ (VerticalScaleOpen W s) (verticalOriginalMap W s z) := by
  have hx0 : WeierstrassDilatation.scaleReesChartEquiv W s b3 b4 b6 h3 h4 h6
      (IsRegular.of_ne_zero hs)
      (WeierstrassDilatation.fromOriginal W s b3 b4 b6 h3 h4 h6 z) =
        scaleOriginalMap W s z :=
    Subtype.ext (WeierstrassDilatation.scaleReesChartEquiv_fromOriginal
      W s b3 b4 b6 h3 h4 h6 (IsRegular.of_ne_zero hs) z)
  have hy0 : WeierstrassModificationY.verticalReesChartEquiv W s b3 b4 b6 h3 h4 h6 hs
      (WeierstrassModificationY.fromOriginal W s b3 b4 b6 h3 h4 h6 z) =
        verticalOriginalMap W s z :=
    Subtype.ext (WeierstrassModificationY.verticalReesChartEquiv_fromOriginal
      W s b3 b4 b6 h3 h4 h6 hs z)
  rw [← hx0, scaleVerticalTransition_base, ← hy0, ← verticalScaleOpenEquiv_base]
  congr 1
  exact AlgHom.congr_fun (WeierstrassModificationY.toDivided_fromOriginal W s b3 b4 b6 h3 h4 h6
    (IsScalarTower.toAlgHom R _ (WeierstrassModificationY.ScaleOpen W s b3 b4 b6))
    (WeierstrassModificationY.scaleUnit W s b3 b4 b6)
    (WeierstrassModificationY.scaleUnit_val W s b3 b4 b6).symm) z

/-- The actual vertical/scale substitution commutes on the full Proj overlap. -/
@[reassoc] theorem verticalScale_toProj :
    verticalToScale W s b3 b4 b6 h3 h4 h6 hs ≫ scaleProjInclusion W s =
      verticalScaleInclusion W s ≫ verticalProjInclusion W s := by
  rw [verticalToScale, verticalScaleTransitionIso_def, Category.assoc]
  exact BlowupRees.originalPreservingTransition_inclusion I (algebraMap R A s)
    (Ideal.subset_span (by simp)) oy (Ideal.subset_span (by simp))
    (scaleVerticalTransition W s b3 b4 b6 h3 h4 h6 hs).toRingHom
    (scaleVerticalTransition_original W s b3 b4 b6 h3 h4 h6 hs)

end FLT.Mazur.WeierstrassModificationReesCoordinates
