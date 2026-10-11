/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveCenterScaling
public import FLT.Mazur.WeierstrassLeftSmoothChartCenterEquality

/-!
# Unit successive centers for original infinity inputs

The deeper original center is the scale times the successive center.
If its translated output is a unit ideal, the successive center is a unit
ideal too. Ring presentations need no chosen coefficient algebra.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R]

variable (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (h3 : W.a₃ = s * (π * b3)) (h4 : W.a₄ = s * (π * b4))
  (h6 : W.a₆ = s ^ 2 * (π ^ 2 * b6))
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "c" =>
  WeierstrassDilatation.fromOriginal W s (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6
local notation "I" => modificationCenter W s π b3 b4 b6
variable {S : Type u} [CommRing S]

/-- The original deeper center retains its exact scaled ideal under any ring presentation. -/
theorem originalCenter_map_ringPresentation (α : B →+* S) :
    (WeierstrassIntegralChart.modificationChartCenter W (s * π) 2).map
        (α.comp (c).toRingHom) =
      Ideal.span {α (algebraMap R B s)} * (I).map α := by
  rw [← Ideal.map_map, originalCenter_map_fromOriginal, Ideal.map_mul, Ideal.map_span]
  simp only [Set.image_singleton]

/-- A unit original deeper center forces the full normalized successive center to be a unit. -/
theorem successiveCenter_eq_top_of_original (α : B →+* S)
    (h : (WeierstrassIntegralChart.modificationChartCenter W (s * π) 2).map
      (α.comp (c).toRingHom) = ⊤) : (I).map α = ⊤ := by
  rw [originalCenter_map_ringPresentation] at h
  exact top_unique (h ▸ Ideal.mul_le_right)

include h3 h4 h6 in
/-- Original X or Y inputs have unit translated successive centers on divided outputs. -/
theorem successiveInfinityPresentation_center (j : Fin 3) (hj : j = 0 ∨ j = 1)
    (p : Spec (.of S) ⟶ (WeierstrassIntegralChart.integralSmoothOpen W).toScheme)
    (α : B →+* S) (β : WeierstrassIntegralChart.Coordinate W j →+* S)
    (hp : p ≫ WeierstrassIntegralChart.integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom β) ≫ WeierstrassIntegralChart.integralCurveChart W j) ≫
        WeierstrassIntegralChart.integralCurveStructure W)
    (hα : Spec.map (CommRingCat.ofHom (α.comp (c).toRingHom)) ≫
        WeierstrassIntegralChart.integralCurveChart W 2 =
      WeierstrassIntegralChart.leftSmoothPointAddition W p
        (Spec.map (CommRingCat.ofHom β) ≫ WeierstrassIntegralChart.integralCurveChart W j) hp) :
    (I).map α = ⊤ := by
  apply successiveCenter_eq_top_of_original W s π b3 b4 b6 h3 h4 h6
  apply WeierstrassIntegralChart.leftSmoothChartPresentation_center_eq_top
    W (s * π) b3 b4 (s * π * b6)
    (by simpa only [mul_assoc] using h3) (by simpa only [mul_assoc] using h4)
    _ j 2 hj p _ β hp hα
  calc
    W.a₆ = s ^ 2 * (π ^ 2 * b6) := h6
    _ = s * π * (s * π * b6) := by ring

end FLT.Mazur.WeierstrassSuccessiveX
