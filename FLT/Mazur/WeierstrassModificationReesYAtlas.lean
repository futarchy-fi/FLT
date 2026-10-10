/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesContraction
public import FLT.Mazur.WeierstrassModificationReesYScaleScheme
public import FLT.Mazur.WeierstrassModificationYOpenImmersion

/-!
# The vertical fraction chart in the global fraction atlas

The descended equation y-chart gives an open immersion of the actual vertical
fraction chart. Its two restrictions are the actual Rees fraction transitions.
The map retains the original cubic contraction on the whole vertical chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The actual vertical fraction spectrum maps into the global fraction atlas. -/
def verticalChart : Spec (.of (WeierstrassModificationY.verticalReesChart W s)) ⟶
    fractionAtlas W s b3 b4 b6 h3 h4 h6 hs :=
  (verticalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
    WeierstrassModificationY.yChart W s b3 b4 b6 ≫
      (fractionAtlasIso W s b3 b4 b6 h3 h4 h6 hs).inv

instance verticalChart_isOpenImmersion :
    IsOpenImmersion (verticalChart W s b3 b4 b6 h3 h4 h6 hs) := by
  let _ : IsOpenImmersion (verticalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom :=
    IsOpenImmersion.of_isIso _
  let _ : IsOpenImmersion (fractionAtlasIso W s b3 b4 b6 h3 h4 h6 hs).inv :=
    IsOpenImmersion.of_isIso _
  exact IsOpenImmersion.comp _ _

/-- The global comparison retains the descended equation y-chart. -/
@[reassoc] theorem verticalChart_atlasIso :
    verticalChart W s b3 b4 b6 h3 h4 h6 hs ≫
        (fractionAtlasIso W s b3 b4 b6 h3 h4 h6 hs).hom =
      (verticalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        WeierstrassModificationY.yChart W s b3 b4 b6 := by
  simp only [verticalChart, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The horizontal restriction is the actual fraction-chart transition. -/
@[reassoc] theorem verticalChart_horizontal :
    verticalHorizontalInclusion W s ≫ verticalChart W s b3 b4 b6 h3 h4 h6 hs =
      verticalToHorizontal W s b3 b4 b6 h3 h4 h6 hs ≫
        horizontalChart W s b3 b4 b6 h3 h4 h6 hs := by
  apply (cancel_mono (fractionAtlasIso W s b3 b4 b6 h3 h4 h6 hs).hom).mp
  rw [Category.assoc, Category.assoc, verticalChart_atlasIso, horizontalChart_atlasIso,
    verticalHorizontalSchemeIso_inclusion_assoc, verticalHorizontalSchemeIso_toChart_assoc,
    WeierstrassModificationY.horizontal_yChart]
  rfl

/-- The scale restriction is the actual fraction-chart transition. -/
@[reassoc] theorem verticalChart_scale :
    verticalScaleInclusion W s ≫ verticalChart W s b3 b4 b6 h3 h4 h6 hs =
      verticalToScale W s b3 b4 b6 h3 h4 h6 hs ≫
        scaleChart W s b3 b4 b6 h3 h4 h6 hs := by
  apply (cancel_mono (fractionAtlasIso W s b3 b4 b6 h3 h4 h6 hs).hom).mp
  rw [Category.assoc, Category.assoc, verticalChart_atlasIso, scaleChart_atlasIso,
    verticalScaleSchemeIso_inclusion_assoc, verticalScaleSchemeIso_toChart_assoc,
    WeierstrassModificationY.scale_yChart]
  rfl

/-- The vertical chart comparison retains every original cubic function. -/
@[reassoc] theorem verticalChartIso_toCurve :
    (verticalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        WeierstrassModificationY.toCurve W s b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom (verticalOriginalMap W s)) ≫
          WeierstrassIntegralChart.integralCurveChart W 2 := by
  change Spec.map _ ≫ (Spec.map _ ≫ _) = _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact WeierstrassModificationY.verticalReesChartEquiv_fromOriginal
    W s b3 b4 b6 h3 h4 h6 hs a

/-- The whole vertical fraction chart contracts by its original algebra structure. -/
@[reassoc] theorem verticalChart_contraction :
    verticalChart W s b3 b4 b6 h3 h4 h6 hs ≫
        fractionContraction W s b3 b4 b6 h3 h4 h6 hs =
      Spec.map (CommRingCat.ofHom (verticalOriginalMap W s)) ≫
          WeierstrassIntegralChart.integralCurveChart W 2 := by
  rw [fractionContraction, verticalChart_atlasIso_assoc,
    WeierstrassModificationY.yChart_contraction, verticalChartIso_toCurve]

end FLT.Mazur.WeierstrassModificationReesCoordinates
