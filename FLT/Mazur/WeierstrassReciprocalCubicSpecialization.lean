/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassReciprocalChartSpecialization

/-!
# Reversed cubic relations on specialized reciprocal charts

Expose the reciprocal divided difference and the unit of the selected denominator,
for both secant and tangent choices and after arbitrary algebra specialization.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

variable (b : Bool) (f : additionChartRing W (reciprocalIndex b) →ₐ[R] S)

/-- The divided difference also survives arbitrary algebra specialization. -/
theorem reciprocalSpecialization_cubic :
    let x₁ := f (reciprocalInputLeft W b (coord W 2 0))
    let x₂ := f (reciprocalInputRight W b (coord W 2 0))
    let y₁ := f (reciprocalInputLeft W b (coord W 2 1))
    let y₂ := f (reciprocalInputRight W b (coord W 2 1))
    let V := (W.map (algebraMap R S)).toAffine
    f (reciprocalChartSlope W b) *
        (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + V.a₂ * (x₁ + x₂) + V.a₄ - V.a₁ * y₁) =
      y₁ + y₂ + V.a₁ * x₂ + V.a₃ := by
  simpa only [reciprocalInputLeft, reciprocalInputRight, AlgHom.comp_apply,
    productX₁, productX₂, productY₁, productY₂, tangentDenominator, tangentNumerator,
    map_sub, map_add, map_mul, map_pow,
    AlgHom.commutes, WeierstrassCurve.toAffine, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄] using
      congrArg f (reciprocalChartSlope_cubic W b)

/-- One of the two actual reversed denominators is a unit on every reciprocal chart. -/
theorem reciprocalSpecialization_denominator_unit :
    let x₁ := f (reciprocalInputLeft W b (coord W 2 0))
    let x₂ := f (reciprocalInputRight W b (coord W 2 0))
    let y₁ := f (reciprocalInputLeft W b (coord W 2 1))
    let y₂ := f (reciprocalInputRight W b (coord W 2 1))
    let V := (W.map (algebraMap R S)).toAffine
    IsUnit (y₁ - y₂) ∨
      IsUnit (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + V.a₂ * (x₁ + x₂) + V.a₄ - V.a₁ * y₁) := by
  cases b with
  | false => exact Or.inl (reciprocalSpecialization_secant_unit W f)
  | true =>
    apply Or.inr
    simpa only [reciprocalInputLeft, reciprocalInputRight, AlgHom.comp_apply,
      productX₁, productX₂, productY₁, Bool.true_eq, ite_true, tangentNumerator,
      map_sub, map_add, map_mul, map_pow, AlgHom.commutes, WeierstrassCurve.toAffine,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄] using
        (reciprocalChartDenominator_isUnit W true).map f

end FLT.Mazur.WeierstrassIntegralChart
