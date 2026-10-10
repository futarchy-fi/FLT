/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassCoefficientAffineProduct

/-!
# Coefficient extension on the actual secant addition chart

Localization of the original coefficient map preserves the regular slope.
The actual addition formulas therefore commute with arbitrary base change.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

open scoped TensorProduct

instance secantChartScalarAlgebra (V : WeierstrassCurve S) : Algebra R (SecantChart V) :=
  inferInstanceAs (Algebra R (Localization.Away (secantDenominator V)))

instance secantChartScalarTower (V : WeierstrassCurve S) :
    IsScalarTower R S (SecantChart V) :=
  inferInstanceAs (IsScalarTower R S (Localization.Away (secantDenominator V)))

/-- The coefficient image of the secant denominator is a unit on the new secant chart. -/
theorem secantCoefficient_denominator_isUnit :
    IsUnit ((((secantRestriction (W.map (algebraMap R S))).restrictScalars R).comp
      (affineProductCoefficientMap W)) (secantDenominator W)) := by
  rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, affineProductCoefficientMap_denominator]
  exact IsLocalization.Away.algebraMap_isUnit (secantDenominator (W.map (algebraMap R S)))

/-- Coefficient extension of the original localized secant algebra. -/
def secantCoefficientMap : SecantChart W →ₐ[R] SecantChart (W.map (algebraMap R S)) :=
  IsLocalization.Away.liftAlgHom (secantDenominator W)
    (secantCoefficient_denominator_isUnit W)

/-- The localized coefficient map retains the actual affine input substitution. -/
theorem secantCoefficientMap_restriction (a : AffineProduct W) :
    secantCoefficientMap (S := S) W (secantRestriction W a) =
      secantRestriction (W.map (algebraMap R S)) (affineProductCoefficientMap W a) :=
  IsLocalization.Away.lift_eq _ (secantCoefficient_denominator_isUnit W) _

/-- The regular secant slope is unchanged by coefficient extension. -/
theorem secantCoefficientMap_slope :
    secantCoefficientMap (S := S) W (secantSlope W) =
      secantSlope (W.map (algebraMap R S)) := by
  have hs := congrArg (secantCoefficientMap (S := S) W) (secantSlope_relation W)
  simp only [map_mul, map_sub, secantCoefficientMap_restriction,
    affineProductCoefficientMap_x₁, affineProductCoefficientMap_x₂,
    affineProductCoefficientMap_y₁, affineProductCoefficientMap_y₂] at hs
  have hu : IsUnit (secantRestriction (W.map (algebraMap R S))
      (secantDenominator (W.map (algebraMap R S)))) :=
    IsLocalization.Away.algebraMap_isUnit _
  apply hu.mul_left_inj.mp
  simpa only [secantDenominator, map_sub] using
    hs.trans (secantSlope_relation (W.map (algebraMap R S))).symm

/-- Actual secant addition commutes with coefficient extension on coordinate algebras. -/
theorem secantCoefficientMap_addition :
    (secantCoefficientMap (S := S) W).comp (secantAddition W) =
      ((secantAddition (W.map (algebraMap R S))).restrictScalars R).comp
        (chartCoefficientMap W 2) := by
  apply hom_ext
  intro i
  fin_cases i
  all_goals
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, chartCoefficientMap_coord,
      secantAddition_coord, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Fin.reduceFinMk, Matrix.head_cons, Matrix.tail_cons,
      WeierstrassCurve.toAffine, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, map_add, map_sub, map_mul, map_pow, map_neg,
      map_one, AlgHom.commutes, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, secantCoefficientMap_restriction,
      affineProductCoefficientMap_x₁, affineProductCoefficientMap_x₂,
      affineProductCoefficientMap_y₁, secantCoefficientMap_slope,
      ← IsScalarTower.algebraMap_apply R S]

end FLT.Mazur.WeierstrassIntegralChart
