/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothCenterInvariant
public import FLT.Mazur.BlowupFractionPrincipalIdeal

/-!
# Exact center equality on affine presentations of the smooth action

An actual affine presentation of the original smooth translation retains the
full center ideal, including nilpotents. On a modified input chart, the output
center is therefore the retained input denominator ideal. The presentation
hypothesis identifies the original action, not a putative modified action.
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
/-- The full global center equality gives equality of the original affine coordinate ideals. -/
theorem leftSmoothAffinePresentation_center_eq
    (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
    (α β : Coordinate W 2 →+* S)
    (hp : p ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) ≫ integralCurveStructure W)
    (hα : Spec.map (CommRingCat.ofHom α) ≫ integralCurveChart W 2 =
      leftSmoothPointAddition W p (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) hp) :
    (modificationChartCenter W s 2).map α = (modificationChartCenter W s 2).map β := by
  have he := leftSmoothPointAddition_center_eq W s b3 b4 b6 h3 h4 h6 p
    (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) hp
  rw [← hα] at he
  simp only [comap_comp, modificationCenterSheaf_chart, modificationChartCenterSheaf,
    BaseAdicThickening.baseIdeal_comap_specMap] at he
  exact le_antisymm ((BaseAdicThickening.baseIdeal_le_iff _ _ _).mp he.le)
    ((BaseAdicThickening.baseIdeal_le_iff _ _ _).mp he.ge)

include h3 h4 h6 in
/-- On an actual fraction input the output center is its retained denominator ideal. -/
theorem leftSmoothFractionPresentation_center_eq
    (f : Coordinate W 2) (hf : f ∈ modificationChartCenter W s 2)
    (ψ : BlowupFractionChart.chart (modificationChartCenter W s 2) f →+* S)
    (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
    (α : Coordinate W 2 →+* S)
    (hp : p ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap _ _))) ≫ integralCurveChart W 2) ≫
        integralCurveStructure W)
    (hα : Spec.map (CommRingCat.ofHom α) ≫ integralCurveChart W 2 =
      leftSmoothPointAddition W p
        (Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap _ _))) ≫ integralCurveChart W 2) hp) :
    (modificationChartCenter W s 2).map α =
      Ideal.span {ψ (BlowupFractionChart.denominator (modificationChartCenter W s 2) f)} := by
  rw [leftSmoothAffinePresentation_center_eq W s b3 b4 b6 h3 h4 h6 p α
    (ψ.comp (algebraMap _ _)) hp hα]
  exact BlowupFractionChart.center_map_eq_mapped_denominator _ f hf ψ

end FLT.Mazur.WeierstrassIntegralChart
