/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothAffineCenterEquality

/-!
# Exact center equality across different original projective charts

The full invariant center may be compared using different affine presentations
for input and output. In particular an original X or Y input has unit center,
even when its output lies in the affine singular-origin chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Scheme.IdealSheafData

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s * b6)
  {S : Type u} [CommRing S]

include h3 h4 h6 in
/-- The actual action preserves full center ideals across arbitrary original chart changes. -/
theorem leftSmoothChartPresentation_center_eq (j k : Fin 3)
    (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
    (α : Coordinate W k →+* S) (β : Coordinate W j →+* S)
    (hp : p ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W j) ≫ integralCurveStructure W)
    (hα : Spec.map (CommRingCat.ofHom α) ≫ integralCurveChart W k =
      leftSmoothPointAddition W p (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W j) hp) :
    (modificationChartCenter W s k).map α = (modificationChartCenter W s j).map β := by
  have he := leftSmoothPointAddition_center_eq W s b3 b4 b6 h3 h4 h6 p
    (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W j) hp
  rw [← hα] at he
  simp only [comap_comp, modificationCenterSheaf_chart, modificationChartCenterSheaf,
    BaseAdicThickening.baseIdeal_comap_specMap] at he
  exact le_antisymm ((BaseAdicThickening.baseIdeal_le_iff _ _ _).mp he.le)
    ((BaseAdicThickening.baseIdeal_le_iff _ _ _).mp he.ge)

include h3 h4 h6 in
/-- An original X or Y input has unit output center on every original output chart. -/
theorem leftSmoothChartPresentation_center_eq_top (j k : Fin 3) (hj : j = 0 ∨ j = 1)
    (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
    (α : Coordinate W k →+* S) (β : Coordinate W j →+* S)
    (hp : p ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W j) ≫ integralCurveStructure W)
    (hα : Spec.map (CommRingCat.ofHom α) ≫ integralCurveChart W k =
      leftSmoothPointAddition W p (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W j) hp) :
    (modificationChartCenter W s k).map α = ⊤ := by
  rw [leftSmoothChartPresentation_center_eq W s b3 b4 b6 h3 h4 h6 j k p α β hp hα,
    modificationChartCenter_eq_top W s j hj, Ideal.map_top]

end FLT.Mazur.WeierstrassIntegralChart
