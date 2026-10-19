/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluSourceLocalization

/-!
# An explicit denominator open for the original Vélu formulas

The product of the reduced x and slope denominators gives an actual affine
function. Its principal localization carries both original rational functions.
-/

@[expose] public noncomputable section

open scoped Polynomial
open RatFunc FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The actual source function cutting out the common denominator open. -/
def veluAffineDenominator : Coordinate E 2 :=
  Polynomial.aeval (coord E 2 0) ((xFunction E G).denom * (slopeFunction E G).denom)

/-- The denominator is nonzero in the original affine coordinate ring. -/
theorem veluAffineDenominator_ne_zero : veluAffineDenominator E G ≠ 0 := by
  intro h
  have he := congrArg (sourceGenericChart E) h
  rw [veluAffineDenominator, sourceGenericChart_polynomial, map_zero] at he
  exact ((algebraMap K⟮X⟯ (FunctionField E)).injective.ne
    (RatFunc.algebraMap_ne_zero
      (mul_ne_zero (xFunction E G).denom_ne_zero (slopeFunction E G).denom_ne_zero))) he

/-- The coordinate ring of the explicit principal open in the original affine cubic. -/
abbrev VeluAffineLocalization := Localization.Away (veluAffineDenominator E G)

/-- The original field comparison on the denominator open. -/
def veluAffineLocalizationHom : VeluAffineLocalization E G →ₐ[K] FunctionField E :=
  sourceLocalizationHom E _ (veluAffineDenominator_ne_zero E G)

/-- The denominator-open coordinates still inject into the original function field. -/
theorem veluAffineLocalizationHom_injective :
    Function.Injective (veluAffineLocalizationHom E G) :=
  sourceLocalizationHom_injective E _ _

/-- Evaluation of a polynomial numerator divided by the common denominator. -/
def veluAffineFraction (p : K[X]) : VeluAffineLocalization E G :=
  algebraMap _ _ (Polynomial.aeval (coord E 2 0) p) *
    IsLocalization.Away.invSelf (veluAffineDenominator E G)

/-- The localized fraction retains its precise value in the original quadratic model. -/
theorem veluAffineFraction_generic (p : K[X]) :
    veluAffineLocalizationHom E G (veluAffineFraction E G p) =
      liftX E (algebraMap K[X] K⟮X⟯ p /
        algebraMap K[X] K⟮X⟯ ((xFunction E G).denom * (slopeFunction E G).denom)) := by
  rw [veluAffineFraction, veluAffineLocalizationHom, map_mul,
    sourceLocalizationHom_algebraMap, sourceLocalizationHom_invSelf,
    veluAffineDenominator, sourceGenericChart_polynomial, sourceGenericChart_polynomial]
  simp only [liftX]
  rw [map_div₀]
  rfl

/-- The original rational x-coordinate, now regular on the explicit principal open. -/
def veluAffineX : VeluAffineLocalization E G :=
  veluAffineFraction E G ((xFunction E G).num * (slopeFunction E G).denom)

/-- The original rational slope, now regular on the explicit principal open. -/
def veluAffineSlope : VeluAffineLocalization E G :=
  veluAffineFraction E G ((slopeFunction E G).num * (xFunction E G).denom)

/-- The regular x-coordinate is exactly the original generic x-coordinate. -/
theorem veluAffineX_generic :
    veluAffineLocalizationHom E G (veluAffineX E G) = liftX E (xFunction E G) := by
  rw [veluAffineX, veluAffineFraction_generic]
  congr 1
  rw [map_mul, map_mul, mul_div_mul_right _ _
    (RatFunc.algebraMap_ne_zero (slopeFunction E G).denom_ne_zero),
    RatFunc.num_div_denom]

/-- The regular slope is exactly the original generic slope. -/
theorem veluAffineSlope_generic :
    veluAffineLocalizationHom E G (veluAffineSlope E G) = liftX E (slopeFunction E G) := by
  rw [veluAffineSlope, veluAffineFraction_generic]
  congr 1
  rw [map_mul, map_mul, mul_comm (algebraMap K[X] K⟮X⟯ (xFunction E G).denom),
    mul_div_mul_right _ _ (RatFunc.algebraMap_ne_zero (xFunction E G).denom_ne_zero),
    RatFunc.num_div_denom]

end WeierstrassCurve.Velu
