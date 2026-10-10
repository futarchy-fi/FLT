/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassVariableChangeAffineProduct
public import FLT.Mazur.WeierstrassVariableChangeAdditionFormula

/-!
# Admissible changes preserve the actual secant chart

Localize the original input substitution at its unit-scaled denominator.
The resulting map carries the actual regular slope to u*l+s.
-/

@[expose] public noncomputable section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)

/-- The transformed secant denominator is invertible on the original secant chart. -/
theorem secantVariableChange_denominator_isUnit :
    IsUnit (((secantRestriction V).comp (affineProductVariableChange W V C h))
      (secantDenominator W)) := by
  rw [AlgHom.comp_apply, affineProductVariableChange_denominator, map_mul, map_pow,
    AlgHom.commutes]
  exact ((C.u.isUnit.map (algebraMap R (SecantChart V))).pow 2).mul
    (IsLocalization.Away.algebraMap_isUnit (secantDenominator V))

/-- The actual map of secant coordinate algebras induced by the admissible change. -/
def secantVariableChange : SecantChart W →ₐ[R] SecantChart V :=
  IsLocalization.Away.liftAlgHom (secantDenominator W)
    (secantVariableChange_denominator_isUnit W V C h)

/-- The localized change extends the original product substitution exactly. -/
theorem secantVariableChange_restriction (a : AffineProduct W) :
    secantVariableChange W V C h (secantRestriction W a) =
      secantRestriction V (affineProductVariableChange W V C h a) :=
  IsLocalization.Away.lift_eq _ (secantVariableChange_denominator_isUnit W V C h) _

/-- The actual localized substitution has the expected regular slope. -/
theorem secantVariableChange_slope :
    secantVariableChange W V C h (secantSlope W) =
      algebraMap R _ (C.u : R) * secantSlope V + algebraMap R _ C.s := by
  have hs := congrArg (secantVariableChange W V C h) (secantSlope_relation W)
  simp only [map_mul, map_sub, secantVariableChange_restriction,
    affineProductVariableChange_x₁, affineProductVariableChange_x₂,
    affineProductVariableChange_y₁, affineProductVariableChange_y₂,
    map_add, map_pow, AlgHom.commutes] at hs
  have ht := WeierstrassVariableChangeAdditionFormula.line_relation
    (C.map (algebraMap R (SecantChart V)))
    (secantRestriction V (productX₁ V)) (secantRestriction V (productX₂ V))
    (secantRestriction V (productY₁ V)) (secantRestriction V (productY₂ V))
    (secantSlope V) (secantSlope_relation V)
  simp only [VariableChange.map, Units.coe_map, MonoidHom.coe_ofClass] at ht
  apply (secantVariableChange_denominator_isUnit W V C h).mul_left_inj.mp
  simpa only [AlgHom.comp_apply, secantDenominator, map_sub,
    affineProductVariableChange_x₁, affineProductVariableChange_x₂, map_add, map_mul,
    map_pow, AlgHom.commutes] using hs.trans ht.symm

end FLT.Mazur.WeierstrassIntegralChart
