/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioAffine
public import FLT.Mazur.WeierstrassDividedFullInfinityFactorRatioMap

/-!
# Full original infinity charts at every arithmetic quotient order

The independently constructed canonical root and the original arithmetic ideal
supply the entire infinity comparison. Its exact projective transition agrees
with the full original initial affine map, retaining the normalized smoothing.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s)
  (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
  (h3a : π ∣ W.a₃) (h4a : π ∣ W.a₄) (h6a : π ∣ W.a₆) (k : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)
local notation "τ" => arithmeticInitialMobiusSmoothing W ha s π m
local notation "hn" => Fact.mk (arithmeticInitialFactorRatioSmoothing_nilpotent W ha s π m hs)
local notation "r" => polynomialSlopeRoot (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6)
local notation "hr" => polynomialSlopeRoot_equation (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6)
local notation "hm" => polynomialSlopeRoot_mem (W.map q) (q b3) (q b4) (q b6) J
  (arithmeticParameterIdeal_nilpotent π m) (ha.map q) (arithmeticCoefficient_mem π m h2)
  (arithmeticCoefficient_mem π m h3) (arithmeticCoefficient_mem π m h4)
  (arithmeticCoefficient_mem π m h6)

/-- The entire original infinity chart over the actual arithmetic quotient maps to the polygon. -/
def arithmeticFactorRatioInfinityPolygonMap :
    Spec (.of (WeierstrassIntegralChart.Coordinate (W.map q) 1)) ⟶
      arithmeticFactorRatioPolygon π m W s ha hs k := by
  let _ := hn
  exact fullFactorRatioInfinityPolygonMap (W.map q) (q s) τ k (q b3) r J
    (arithmeticParameterIdeal_nilpotent π m) hm (arithmeticCoefficient_mem π m h3)
    (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3a)
    (arithmeticCoefficient_mem π m h4a) (arithmeticCoefficient_mem π m h6a)

variable (h₃ : W.a₃ = s * b3) (h₄ : W.a₄ = s * b4) (h₆ : W.a₆ = s ^ 2 * b6)

/-- The actual original arithmetic projective transition on the entire initial D(y). -/
def arithmeticFactorRatioInfinityTransition :=
  initialInfinityTransition (W.map q) (q s) (q b3) (q b4) (q b6)
    (by simpa only [WeierstrassCurve.map_a₃, map_mul] using congrArg q h₃)
    (by simpa only [WeierstrassCurve.map_a₄, map_mul] using congrArg q h₄)
    (by simpa only [WeierstrassCurve.map_a₆, map_mul, map_pow] using congrArg q h₆)

/-- Both full original arithmetic charts agree along their unchanged projective transition. -/
@[reassoc] theorem arithmeticFactorRatioInfinityPolygonMap_initial :
    Spec.map (CommRingCat.ofHom
      (arithmeticFactorRatioInfinityTransition π m W s b3 b4 b6 h₃ h₄ h₆).toRingHom) ≫
        arithmeticFactorRatioInfinityPolygonMap π m W s b3 b4 b6
          ha hs h2 h3 h4 h6 h3a h4a h6a k =
      polynomialInitialInfinityInclusion (W.map q) (q s) (q b3) (q b4) (q b6) ≫
        arithmeticFactorRatioAffinePolygonMap π m W s b3 b4 b6 ha hs h2 h3 h4 h6 k := by
  let _ := hn
  unfold arithmeticFactorRatioInfinityPolygonMap arithmeticFactorRatioInfinityTransition
    arithmeticFactorRatioAffinePolygonMap canonicalFactorRatioAffinePolygonMap
  exact fullFactorRatioInfinityPolygonMap_initial (W.map q) (ha.map q) (q s) τ
    (initialTangentSmoothing_factor (W.map q) (ha.map q) (q s)) k (q b3) (q b4) (q b6)
    r hr J (arithmeticParameterIdeal_nilpotent π m) hm (arithmeticCoefficient_mem π m h3)
    (arithmeticCoefficient_mem π m h2) (arithmeticCoefficient_mem π m h3a)
    (arithmeticCoefficient_mem π m h4a) (arithmeticCoefficient_mem π m h6a) _ _ _

end FLT.Mazur.WeierstrassDividedDepth
