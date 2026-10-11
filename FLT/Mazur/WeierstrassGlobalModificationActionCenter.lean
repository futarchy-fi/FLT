/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationLocalAction

/-!
# Regular output centers on the complete action cover

Every affine-output member has a regular principal output center. Fraction
inputs retain their original denominator, while infinity inputs use 1.
These are properties of the actual source cover, including exceptional inputs.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The retained principal denominator on each actual action-source member. -/
def smoothActionDenominator (i : (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).I₀) :
    (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).X i :=
  match i with
  | ⟨none, _⟩ => 1
  | ⟨some k, j⟩ =>
    fractionSmoothOriginalHom W s (centerGenerators W s k) j (centerGenerators W s k)

/-- The retained denominator is regular everywhere on its actual source member. -/
theorem smoothActionDenominator_regular
    (i : (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).I₀) :
    IsRegular (smoothActionDenominator W s b3 b4 b6 h3 h4 h6 hs i) := by
  rcases i with ⟨k, j⟩
  cases k with
  | none => exact isRegular_one
  | some k => exact fractionSmoothOriginalHom_regular W s (centerGenerators W s k) j

/-- The full affine output center equals the ideal of the actual retained regular denominator. -/
theorem smoothActionOutput_center
    (i : (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).I₀)
    (hi : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 2) :
    (modificationChartCenter W s 2).map
        (modifiedSmoothOutputHomAt W (originalInputContraction W s i.1) i.2 2 hi) =
      Ideal.span {smoothActionDenominator W s b3 b4 b6 h3 h4 h6 hs i} := by
  rcases i with ⟨k, j⟩
  cases k with
  | none =>
    exact (infinitySmoothOutput_center W s b3 b4 (s * b6) h3 h4
      (by simpa only [pow_two, mul_assoc] using h6) j hi).trans Ideal.span_singleton_one.symm
  | some k =>
    exact fractionSmoothPresentation_center W s b3 b4 (s * b6) h3 h4
      (by simpa only [pow_two, mul_assoc] using h6)
      (centerGenerators W s k) (centerGenerators_mem W s k) j hi

/-- Affine-output local lifts retain the exact affine-coordinate factorization. -/
@[reassoc] theorem smoothActionLocal_affine_contraction
    (i : (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).I₀)
    (hi : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 2) :
    smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs =
      Spec.map (CommRingCat.ofHom
        (modifiedSmoothOutputHomAt W (originalInputContraction W s i.1) i.2 2 hi)) ≫
          integralCurveChart W 2 := by
  rw [smoothActionLocal_contraction, smoothActionCover_original,
    modifiedSmoothAffineCover_addition, modifiedSmoothOutputHomAt_addition]

end FLT.Mazur.WeierstrassGlobalModification
