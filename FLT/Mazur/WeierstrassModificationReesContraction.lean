/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesGluing

/-!
# The fraction atlas retains the original contraction

The global isomorphism preserves the map to the original cubic. On either
fraction chart that map is induced by its original coordinate algebra structure.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The original coordinate functions in the horizontal fraction chart. -/
def horizontalOriginalMap : WeierstrassIntegralChart.Coordinate W 2 →+*
    WeierstrassModificationX.horizontalReesChart W s :=
  algebraMap _ (BlowupFractionChart.chart (WeierstrassDilatation.modificationCenter W s)
    (WeierstrassIntegralChart.coord W 2 0))

/-- The original coordinate functions in the scale fraction chart. -/
def scaleOriginalMap : WeierstrassIntegralChart.Coordinate W 2 →+*
    WeierstrassDilatation.scaleReesChart W s :=
  algebraMap _ (BlowupFractionChart.chart (WeierstrassDilatation.modificationCenter W s)
    (algebraMap R (WeierstrassIntegralChart.Coordinate W 2) s))

/-- The original coordinate functions in the vertical fraction chart. -/
def verticalOriginalMap : WeierstrassIntegralChart.Coordinate W 2 →+*
    WeierstrassModificationY.verticalReesChart W s :=
  algebraMap _ (BlowupFractionChart.chart (WeierstrassDilatation.modificationCenter W s)
    (WeierstrassIntegralChart.coord W 2 1))

/-- The horizontal fraction chart contracts by its original algebra structure. -/
@[reassoc] theorem horizontalChartIso_toCurve :
    (horizontalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        WeierstrassModificationX.toCurve W s b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom (horizontalOriginalMap W s)) ≫
          WeierstrassIntegralChart.integralCurveChart W 2 := by
  change Spec.map _ ≫ (Spec.map _ ≫ _) = _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact WeierstrassModificationX.horizontalReesChartEquiv_fromOriginal
    W s b3 b4 b6 h3 h4 h6 hs a

/-- The scale fraction chart contracts by its original algebra structure. -/
@[reassoc] theorem scaleChartIso_toCurve :
    (scaleChartIso W s b3 b4 b6 h3 h4 h6 (IsRegular.of_ne_zero hs)).hom ≫
        WeierstrassDilatation.toCurve W s b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom (scaleOriginalMap W s)) ≫
          WeierstrassIntegralChart.integralCurveChart W 2 := by
  change Spec.map _ ≫ (Spec.map _ ≫ _) = _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact WeierstrassDilatation.scaleReesChartEquiv_fromOriginal
    W s b3 b4 b6 h3 h4 h6 (IsRegular.of_ne_zero hs) a

/-- The original cubic contraction on the globally compared fraction atlas. -/
def fractionContraction : fractionAtlas W s b3 b4 b6 h3 h4 h6 hs ⟶
    WeierstrassIntegralChart.integralCurve W :=
  (fractionAtlasIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
    WeierstrassModificationX.contraction W s b3 b4 b6 h3 h4 h6

/-- The comparison is an isomorphism over the original cubic. -/
theorem fractionAtlasIso_contraction :
    (fractionAtlasIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        WeierstrassModificationX.contraction W s b3 b4 b6 h3 h4 h6 =
      fractionContraction W s b3 b4 b6 h3 h4 h6 hs := rfl

/-- The horizontal restriction retains every original cubic function. -/
@[reassoc] theorem horizontalChart_contraction :
    horizontalChart W s b3 b4 b6 h3 h4 h6 hs ≫
        fractionContraction W s b3 b4 b6 h3 h4 h6 hs =
      Spec.map (CommRingCat.ofHom (horizontalOriginalMap W s)) ≫
          WeierstrassIntegralChart.integralCurveChart W 2 := by
  rw [fractionContraction, horizontalChart_atlasIso_assoc,
    WeierstrassModificationX.xChart_contraction, horizontalChartIso_toCurve]

/-- The scale restriction retains every original cubic function. -/
@[reassoc] theorem scaleChart_contraction :
    scaleChart W s b3 b4 b6 h3 h4 h6 hs ≫
        fractionContraction W s b3 b4 b6 h3 h4 h6 hs =
      Spec.map (CommRingCat.ofHom (scaleOriginalMap W s)) ≫
          WeierstrassIntegralChart.integralCurveChart W 2 := by
  rw [fractionContraction, scaleChart_atlasIso_assoc,
    WeierstrassModificationX.dividedChart_contraction,
    scaleChartIso_toCurve W s b3 b4 b6 h3 h4 h6 hs]

end FLT.Mazur.WeierstrassModificationReesCoordinates
