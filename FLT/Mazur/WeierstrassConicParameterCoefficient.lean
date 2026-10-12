/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicParameterOrigin

/-!
# Coefficient maps on the entire rational conic parameter

The denominator and its inverse specialize with the original constant. The
map retains the parameter origin and both inverse conic coordinates.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
  (c : S) (d : T) (hc : f c = d)
local notation "P" => ConicParameterOpen d
local notation "g" => (algebraMap T[X] P).comp (Polynomial.mapRingHom f)

include hc in
/-- The full parameter denominator maps to the target's invertible denominator. -/
theorem conicParameterCoefficient_denominator :
    IsUnit (g (conicParameterPolynomial c)) := by
  have h : Polynomial.map f (conicParameterPolynomial c) = conicParameterPolynomial d := by
    simp only [conicParameterPolynomial, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hc]
  change IsUnit (algebraMap T[X] P (Polynomial.map f (conicParameterPolynomial c)))
  rw [h]
  exact IsLocalization.Away.algebraMap_isUnit (conicParameterPolynomial d)

/-- Coefficient specialization on every regular function of the full parameter open. -/
def conicParameterCoefficientMap : ConicParameterOpen c →+* P :=
  IsLocalization.Away.lift (conicParameterPolynomial c)
    (conicParameterCoefficient_denominator f c d hc)

/-- Every polynomial specializes by its original coefficients. -/
theorem conicParameterCoefficientMap_base (p : S[X]) :
    conicParameterCoefficientMap f c d hc (algebraMap S[X] _ p) =
      algebraMap T[X] P (Polynomial.map f p) :=
  IsLocalization.Away.lift_eq _ _ _

/-- Constants retain the specified coefficient morphism. -/
theorem conicParameterCoefficientMap_scalar (s : S) :
    conicParameterCoefficientMap f c d hc (algebraMap S _ s) = algebraMap T P (f s) := by
  rw [IsScalarTower.algebraMap_apply S S[X], conicParameterCoefficientMap_base]
  change algebraMap T[X] P (Polynomial.map f (C s)) = _
  rw [Polynomial.map_C]
  rfl

/-- The whole parameter coordinate is preserved. -/
@[simp] theorem conicParameterCoefficientMap_z :
    conicParameterCoefficientMap f c d hc (conicParameterZ c) = conicParameterZ d := by
  rw [conicParameterZ, conicParameterCoefficientMap_base, Polynomial.map_X]
  rfl

/-- The inverse of the original denominator specializes without cancellation. -/
@[simp] theorem conicParameterCoefficientMap_inv :
    conicParameterCoefficientMap f c d hc (conicParameterInv c) = conicParameterInv d := by
  have hu : IsUnit (1 - algebraMap T P d * conicParameterZ d ^ 2) :=
    isUnit_of_mul_isUnit_left (by rw [conicParameter_mul_inv d]; exact isUnit_one)
  apply hu.mul_left_cancel
  have h := congrArg (conicParameterCoefficientMap f c d hc) (conicParameter_mul_inv c)
  rw [conicParameter_mul_inv]
  simpa only [map_mul, map_sub, map_one, map_pow, conicParameterCoefficientMap_scalar,
    conicParameterCoefficientMap_z, hc] using h

/-- Incidence in the first inverse chart commutes with coefficient specialization. -/
theorem conicParameterCoefficientMap_inverseT (a : S) :
    conicParameterCoefficientMap f c d hc (conicInverseT a c) = conicInverseT (f a) d := by
  simp only [conicInverseT, map_mul, conicParameterCoefficientMap_scalar,
    conicParameterCoefficientMap_z, conicParameterCoefficientMap_inv]

/-- The entire signed slope in the inverse chart specializes as well. -/
theorem conicParameterCoefficientMap_inverseV (a : S) :
    conicParameterCoefficientMap f c d hc (conicInverseV a c) = conicInverseV (f a) d := by
  simp only [conicInverseV, map_mul, map_pow, conicParameterCoefficientMap_scalar,
    conicParameterCoefficientMap_z, conicParameterCoefficientMap_inv, hc]

/-- The parameter origin is preserved over the coefficient morphism. -/
theorem conicParameterCoefficientMap_origin :
    (conicParameterOrigin d).toRingHom.comp (conicParameterCoefficientMap f c d hc) =
      f.comp (conicParameterOrigin c).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (conicParameterPolynomial c))
  apply Polynomial.ringHom_ext
  · intro s
    change conicParameterOrigin d
      (conicParameterCoefficientMap f c d hc (algebraMap S _ s)) =
        f (conicParameterOrigin c (algebraMap S _ s))
    rw [conicParameterCoefficientMap_scalar, AlgHom.commutes, AlgHom.commutes]
    rfl
  · change conicParameterOrigin d
      (conicParameterCoefficientMap f c d hc (conicParameterZ c)) =
        f (conicParameterOrigin c (conicParameterZ c))
    rw [conicParameterCoefficientMap_z, conicParameterOrigin_z,
      conicParameterOrigin_z, map_zero]

end FLT.Mazur.WeierstrassModificationX
