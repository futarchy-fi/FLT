/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothFractionActionCover
public import FLT.Mazur.RegularCenterQuotientOpenRatios
public import FLT.Mazur.RegularCenterQuotientLinear

/-!
# The actual horizontal input and output action presentation

On the horizontal member of the genuine action cover, the original input X
is the retained regular denominator. Its quotient is exactly one, including
after residue restriction. The input and output maps retain their original
coordinate contractions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s * b6)
  {S : Type u} [CommRing S]
  (p : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme) (α β : Coordinate W 2 →+* S)
  (hp : p ≫ integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) ≫ integralCurveStructure W)
  (hα : Spec.map (CommRingCat.ofHom α) ≫ integralCurveChart W 2 =
    leftSmoothPointAddition W p (Spec.map (CommRingCat.ofHom β) ≫ integralCurveChart W 2) hp)

local notation "I" => modificationChartCenter W s 2
local notation "x" => coord W 2 0
local notation "hx" => WeierstrassModificationReesCoordinates.centerGenerators_mem W s 1
variable (ψ : BlowupFractionChart.chart (modificationChartCenter W s 2) (coord W 2 0) →+* S)
  (hβ : β = ψ.comp
    (algebraMap (Coordinate W 2)
      (BlowupFractionChart.chart (modificationChartCenter W s 2) (coord W 2 0))))
  (hflat : RingHom.Flat
    (R := BlowupFractionChart.chart (modificationChartCenter W s 2) (coord W 2 0)) (S := S) ψ)

open RegularCenter BlowupFractionChart
local notation "z" => ψ (denominator I x)
local notation "O" => LeftSmoothFractionActionOpen W s b3 b4 b6
  h3 h4 h6 p α β hp hα x hx ψ hβ 1
local notation "φ" => algebraMap S O

/-- The original input fraction chart restricted to the actual output horizontal open. -/
def leftSmoothHorizontalInputLift : chart I x →+* O := (φ).comp ψ

include hβ in
/-- The actual horizontal input lift keeps every original input coordinate. -/
theorem leftSmoothHorizontalInputLift_base (t : Coordinate W 2) :
    leftSmoothHorizontalInputLift W s b3 b4 b6 h3 h4 h6 p α β hp hα ψ hβ
      (algebraMap _ _ t) = φ (β t) := by
  change φ (ψ (algebraMap _ _ t)) = φ (β t)
  exact congrArg φ (DFunLike.congr_fun hβ t).symm

include hβ in
/-- The original input X is the retained denominator, before residue restriction. -/
theorem leftSmoothHorizontalInput_denominator : β x = z := by
  rw [hβ]
  rfl

include hβ in
/-- The input center has precisely the same denominator on the actual output open. -/
theorem leftSmoothHorizontalInput_principal : ((I).map β).map φ = Ideal.span {φ z} := by
  have h : (I).map β = Ideal.span {z} := by
    rw [hβ]
    exact center_map_eq_mapped_denominator I x hx ψ
  rw [h, Ideal.map_span, Set.image_singleton]

include hflat in
/-- Flat input presentation and localization retain regularity of the same input denominator. -/
theorem leftSmoothHorizontalInput_regular : IsRegular (φ z) := by
  apply quotientOpen_input_regular
  exact flatRingHom_isRegular ψ hflat (denominator_regular I x)

include hβ hflat in
/-- The input horizontal quotient is one on the actual output action open. -/
theorem leftSmoothHorizontalInput_quotient :
    quotient ((I).map β) φ (φ z)
      (leftSmoothHorizontalInput_principal W s b3 b4 b6 h3 h4 h6 p α β hp hα ψ hβ)
      (β x) (Ideal.mem_map_of_mem β hx) = 1 := by
  symm
  apply quotient_unique _ _ _ _
    (leftSmoothHorizontalInput_regular W s b3 b4 b6 h3 h4 h6 p α β hp hα ψ hβ hflat)
  rw [mul_one, leftSmoothHorizontalInput_denominator W s β ψ hβ]

end FLT.Mazur.WeierstrassIntegralChart
