/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveExteriorCenter

/-!
# Unit successive output centers from regular original input centers

Original smooth addition preserves the deeper center and the coefficient
map. A regular generator dividing the output scale therefore cancels from
the scaled output ideal, forcing the normalized center to be a unit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (h3 : W.a₃ = s * (π * b3)) (h4 : W.a₄ = s * (π * b4))
  (h6 : W.a₆ = s ^ 2 * (π ^ 2 * b6))
local notation "B" => WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "q" => WeierstrassDilatation.fromOriginal W s
  (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6
variable (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
  (α : WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6) →+* S)
  (β : WeierstrassIntegralChart.Coordinate W 2 →+* S)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) ≫ integralCurveStructure W)
  (ha : Spec.map (CommRingCat.ofHom (α.comp
      (WeierstrassDilatation.fromOriginal W s (π * b3) (π * b4) (π ^ 2 * b6)
        h3 h4 h6).toRingHom)) ≫ integralCurveChart W 2 =
    leftSmoothPointAddition W p (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) hp)

include ha in
/-- The normalized output and original input of genuine addition agree on all coefficients. -/
theorem regularInputPresentation_coefficients :
    α.comp (algebraMap R B) = β.comp (algebraMap R (WeierstrassIntegralChart.Coordinate W 2)) := by
  have he := congrArg (fun t => t ≫ integralCurveStructure W) ha
  rw [leftSmoothPointAddition_structure, hp] at he
  simp only [Category.assoc, integralCurveChart_structure, chartStructure] at he
  have out : Spec.map (CommRingCat.ofHom (α.comp (q).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R (WeierstrassIntegralChart.Coordinate W 2))) =
        Spec.map (CommRingCat.ofHom (α.comp (algebraMap R B))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact congrArg α ((q).commutes r)
  rw [out, ← Spec.map_comp] at he
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

include ha in
/-- A regular principal input center dividing the scale forces a unit normalized output center. -/
theorem successiveCenter_unit_of_regularInput (x : S) (hx : IsRegular x)
    (hcenter : (modificationChartCenter W (s * π) 2).map β = Ideal.span {x})
    (hscale : β (algebraMap R _ s) ∈ Ideal.span {x}) :
    (modificationCenter W s π b3 b4 b6).map α = ⊤ := by
  have he := leftSmoothChartPresentation_center_eq W (s * π) b3 b4 (s * π * b6)
    (by simpa only [mul_assoc] using h3) (by simpa only [mul_assoc] using h4)
    (by calc
      W.a₆ = s ^ 2 * (π ^ 2 * b6) := h6
      _ = (s * π) * (s * π * b6) := by ring) 2 2 p _ β hp ha
  rw [originalCenter_map_ringPresentation, hcenter] at he
  have hc := RingHom.congr_fun
    (regularInputPresentation_coefficients W s π b3 b4 b6 h3 h4 h6 p α β hp ha) s
  simp only [RingHom.comp_apply] at hc
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hscale
  rw [hc, ht] at he
  exact successiveCenter_unit_of_scaled_eq x t _ hx he

end FLT.Mazur.WeierstrassSuccessiveX
