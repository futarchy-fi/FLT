/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalAddition

/-!
# Substitution compatibility of integral formal addition

Every step of the construction commutes with substitution of zero-constant
parameters. Consequently the two-variable addition series represents the operation
constructed from the secant, including after setting either variable to zero.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity
open MvPowerSeries

variable {R : Type*} [CommRing R] {σ τ : Type*} (W : WeierstrassCurve R)
variable {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
variable (ha0 : ∀ i, (a i).constantCoeff = 0)

include ha0

/-- Substitution by zero-constant parameters preserves the constant coefficient. -/
theorem constantCoeff_substitution (f : MvPowerSeries σ R) :
    (substAlgHom ha f).constantCoeff = f.constantCoeff := by
  have h := constantCoeff_subst_eq_zero (R := R) (f := f - C f.constantCoeff) ha ha0
    (show (f - C f.constantCoeff).constantCoeff = (0 : R) by simp)
  simpa only [subst_sub ha, map_sub, subst_C, constantCoeff_C, sub_eq_zero,
    coe_substAlgHom] using h

/-- A unit with constant coefficient one has a natural normalized inverse. -/
theorem substitution_invOfUnit {f : MvPowerSeries σ R} (hf : f.constantCoeff = 1) :
    substAlgHom ha (invOfUnit f 1) = invOfUnit (substAlgHom ha f) 1 := by
  have hf' : (substAlgHom ha f).constantCoeff = 1 := by
    rw [constantCoeff_substitution ha ha0, hf]
  have h₁ := congrArg (substAlgHom ha) (mul_invOfUnit f 1 hf)
  have h₂ := mul_invOfUnit (substAlgHom ha f) 1 hf'
  simp only [map_mul, map_one] at h₁
  apply sub_eq_zero.mp
  apply (isUnit_iff_constantCoeff.mpr (hf' ▸ isUnit_one)).mul_right_eq_zero.mp
  linear_combination h₁ - h₂

omit ha0 in
/-- The integral coordinate series commutes with substitution. -/
theorem substitution_coordinate {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    substAlgHom ha (coordinate W t) = coordinate W (substAlgHom ha t) := by
  unfold coordinate PowerSeries.subst
  rw [coe_substAlgHom, subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero ht).const ha]

omit ha0 in
/-- The secant denominator commutes with substitution. -/
theorem substitution_secantDenominator {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    substAlgHom ha (secantDenominator W t v) =
      secantDenominator W (substAlgHom ha t) (substAlgHom ha v) := by
  simp only [secantDenominator, differenceUnit, curve, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, map_sub, map_one, map_mul, map_add, map_pow,
    substitution_coordinate W ha ht, substitution_coordinate W ha hv,
    coe_substAlgHom, subst_C]

/-- The slope commutes with substitution, including on the diagonal. -/
theorem substitution_slope {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    substAlgHom ha (slope W t v) = slope W (substAlgHom ha t) (substAlgHom ha v) := by
  simp only [slope, map_mul, substitution_invOfUnit ha ha0
    (constantCoeff_secantDenominator W ht hv), substitution_secantDenominator W ha ht hv,
    secantNumerator, curve, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₄, map_add, map_pow, substitution_coordinate W ha hv,
    coe_substAlgHom, subst_C]

/-- The intercept commutes with substitution. -/
theorem substitution_intercept {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    substAlgHom ha (intercept W t v) = intercept W (substAlgHom ha t) (substAlgHom ha v) := by
  simp only [intercept, map_sub, map_mul, substitution_coordinate W ha ht,
    substitution_slope W ha ha0 ht hv]

/-- The third intersection parameter commutes with substitution. -/
theorem substitution_thirdParameter {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    substAlgHom ha (thirdParameter W t v) =
      thirdParameter W (substAlgHom ha t) (substAlgHom ha v) := by
  simp only [thirdParameter, map_sub, map_mul, map_neg]
  rw [substitution_invOfUnit ha ha0 (constantCoeff_cubicLeading W ht hv)]
  simp only [cubicLeading, cubicQuadratic, curve, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, map_add, map_mul, map_pow, map_one, map_ofNat,
    substitution_slope W ha ha0 ht hv, substitution_intercept W ha ha0 ht hv,
    coe_substAlgHom, subst_C]

/-- Negation commutes with substitution. -/
theorem substitution_negate {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    substAlgHom ha (negate W t) = negate W (substAlgHom ha t) := by
  simp only [negate, negationUnitInv, map_mul, map_neg]
  rw [substitution_invOfUnit ha ha0 (constantCoeff_negationDenominator W ht)]
  simp only [negationDenominator, curve, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
    map_sub, map_mul, map_one, substitution_coordinate W ha ht,
    coe_substAlgHom, subst_C]

/-- Formal addition commutes with substitution. -/
theorem substitution_add {t v : MvPowerSeries σ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    substAlgHom ha (add W t v) = add W (substAlgHom ha t) (substAlgHom ha v) := by
  rw [add, substitution_negate W ha ha0 (constantCoeff_thirdParameter W ht hv),
    substitution_thirdParameter W ha ha0 ht hv, add]

omit ha0 in
/-- The two-variable series evaluates formally to the constructed operation. -/
theorem additionSeries_subst {t v : MvPowerSeries τ R}
    (ht : t.constantCoeff = 0) (hv : v.constantCoeff = 0) :
    (additionSeries W).subst ![t, v] = add W t v := by
  have ha0 : ∀ i : Fin 2, (![t, v] i).constantCoeff = 0 := by
    intro i
    fin_cases i <;> simpa
  have ha : HasSubst ![t, v] := hasSubst_of_constantCoeff_zero ha0
  rw [← coe_substAlgHom ha, additionSeries, substitution_add W ha ha0 (by simp) (by simp)]
  simp [subst_X ha]

end FLT.Mazur.FormalInfinity
