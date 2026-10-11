/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothTransportedCenter

/-!
# Full center preservation on each complete projective input chart

The second Y-chart misses the center as a scheme. On the second Z-chart,
the two genuine mixed domains reduce to the polynomial law and the proved
transported affine law. Thus all four original input charts preserve the ideal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.IdealSheafData
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s * b6)

include h3 h4 h6 in
/-- Polynomial center containment retains the actual second global input. -/
theorem projectiveAdditionChart_center_le_global (b c : Bool) :
    (modificationCenterSheaf W s).comap
        (Spec.map (CommRingCat.ofHom (projectiveAdditionChart W
          (productChartCoordinate b) (productChartCoordinate c) 2).toRingHom) ≫
            integralCurveChart W 2) ≤
      (modificationCenterSheaf W s).comap
        (projectiveAdditionInclusion W (productChartCoordinate b) (productChartCoordinate c) 2 ≫
          integralCurveProductChart W b c ≫
            pullback.snd (integralCurveStructure W) (integralCurveStructure W)) := by
  rw [integralCurveProductChart_snd, ← Category.assoc, projectiveAdditionInclusion,
    ← Spec.map_comp]
  exact projectiveAdditionChart_center_le W s b3 b4 h3 h4
    (productChartCoordinate b) (productChartCoordinate c) 2 b6 h6

/-- Every input with second point in the Y-chart has unit pulled-back center. -/
theorem leftSmoothInput_center_y (b : Bool) :
    (modificationCenterSheaf W s).comap
      (leftSmoothProductChartInput W b true ≫
        pullback.snd (integralCurveStructure W) (integralCurveStructure W)) = ⊤ := by
  rw [leftSmoothProductChartInput, Category.assoc, integralCurveProductChart_snd]
  have hy := modificationCenterSheaf_chart_eq_top W s
    (productChartCoordinate true) (Or.inr rfl)
  simp only [comap_comp, hy, comap_top]

include h3 h4 h6 in
/-- Each full left smooth input chart preserves the original nonreduced center ideal. -/
theorem leftSmoothInputAddition_center_le (b c : Bool) :
    (modificationCenterSheaf W s).comap (leftSmoothInputAddition W b c) ≤
      (modificationCenterSheaf W s).comap
        (leftSmoothProductChartInput W b c ≫
          pullback.snd (integralCurveStructure W) (integralCurveStructure W)) := by
  cases c with
  | true => rw [leftSmoothInput_center_y]; exact le_top
  | false =>
    let ha : b = false ∨ false = false := Or.inr rfl
    rw [leftSmoothInputAddition_mixed W b false ha]
    apply BaseAdicThickening.idealSheaf_le_of_openCover (leftSmoothMixedCover W b false ha)
    intro d
    rw [← comap_comp, leftSmoothMixedLocal_glued]
    cases d with
    | false =>
      have h := comap_mono (leftSmoothMixedProjection W b false ha false)
        (projectiveAdditionChart_center_le_global W s b3 b4 b6 h3 h4 h6 b false)
      have hi : projectiveAdditionInclusion W (productChartCoordinate b)
          (productChartCoordinate false) 2 = mixedProductCoverInclusion W
            (productChartCoordinate b) (productChartCoordinate false) false := rfl
      simp only [← comap_comp, hi, ← Category.assoc,
        leftSmoothMixedProjection_inputs] at h
      simpa only [← comap_comp, ← Category.assoc,
        leftSmoothMixedLocal, leftSmoothProductChartInput] using h
    | true =>
      have h := comap_mono (leftSmoothMixedAffineLift W b false ha)
        (leftSmoothAffineOverlapAddition_center_le W s b3 b4 h3 h4 b false)
      simpa only [← comap_comp, ← Category.assoc, leftSmoothMixedAffineLift_inputs,
        leftSmoothMixedLocal, leftSmoothProductChartInput] using h

end FLT.Mazur.WeierstrassIntegralChart
