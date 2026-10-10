/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTransport
public import FLT.Mazur.WeierstrassModificationXConicParameterOrigin

/-!
# Negation on the original localized conic parameter

The even denominator is unchanged by parameter negation. This involution
retains the origin and the signed original incidence and slope functions.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (c : R)
local notation "P" => ConicParameterOpen c

/-- Negating the parameter preserves its actual denominator. -/
theorem conicParameterPolynomial_neg :
    algEquivAevalNegX (conicParameterPolynomial c) = conicParameterPolynomial c := by
  simp [conicParameterPolynomial, algEquivAevalNegX]

/-- The original parameter negation on its entire principal open. -/
def conicParameterNeg : P ≃ₐ[R] P :=
  PrincipalOpenTransport.equiv algEquivAevalNegX _ _ (conicParameterPolynomial_neg c)

/-- The involution keeps the substitution on every polynomial. -/
theorem conicParameterNeg_base (p : R[X]) :
    conicParameterNeg c (algebraMap R[X] P p) =
      algebraMap R[X] P (aeval (-X : R[X]) p) :=
  PrincipalOpenTransport.equiv_base _ _ _ _ _

/-- The original parameter changes sign. -/
@[simp] theorem conicParameterNeg_z :
    conicParameterNeg c (conicParameterZ c) = -conicParameterZ c := by
  rw [conicParameterZ, conicParameterNeg_base, aeval_X, map_neg]

/-- Applying parameter negation twice fixes every regular function. -/
theorem conicParameterNeg_involutive :
    (conicParameterNeg c).toAlgHom.comp (conicParameterNeg c).toAlgHom = AlgHom.id R P := by
  apply IsLocalization.algHom_ext (Submonoid.powers (conicParameterPolynomial c))
  apply Polynomial.algHom_ext
  change conicParameterNeg c (conicParameterNeg c (conicParameterZ c)) = conicParameterZ c
  rw [conicParameterNeg_z, map_neg, conicParameterNeg_z, neg_neg]

/-- The inverse denominator is unchanged by parameter negation. -/
@[simp] theorem conicParameterNeg_inv :
    conicParameterNeg c (conicParameterInv c) = conicParameterInv c := by
  have hu : IsUnit (1 - algebraMap R P c * conicParameterZ c ^ 2) :=
    isUnit_of_mul_isUnit_left (by rw [conicParameter_mul_inv c]; exact isUnit_one)
  apply hu.mul_left_cancel
  have h := congrArg (conicParameterNeg c) (conicParameter_mul_inv c)
  rw [conicParameter_mul_inv]
  simpa only [map_mul, map_sub, map_one, map_pow, AlgEquiv.commutes,
    conicParameterNeg_z, neg_sq] using h

/-- The original incidence coordinate changes sign. -/
@[simp] theorem conicParameterNeg_inverseT (a : R) :
    conicParameterNeg c (conicInverseT a c) = -conicInverseT a c := by
  simp only [conicInverseT, map_mul, AlgEquiv.commutes,
    conicParameterNeg_z, conicParameterNeg_inv, mul_neg, neg_mul]

/-- The original slope is unchanged because it is quadratic in the parameter. -/
@[simp] theorem conicParameterNeg_inverseV (a : R) :
    conicParameterNeg c (conicInverseV a c) = conicInverseV a c := by
  simp only [conicInverseV, map_mul, map_pow, AlgEquiv.commutes,
    conicParameterNeg_z, conicParameterNeg_inv, neg_sq]

/-- Parameter negation fixes the entire original origin homomorphism. -/
theorem conicParameterNeg_origin :
    (conicParameterOrigin c).comp (conicParameterNeg c).toAlgHom = conicParameterOrigin c := by
  apply IsLocalization.algHom_ext (Submonoid.powers (conicParameterPolynomial c))
  apply Polynomial.algHom_ext
  change conicParameterOrigin c (conicParameterNeg c (conicParameterZ c)) =
    conicParameterOrigin c (conicParameterZ c)
  rw [conicParameterNeg_z, map_neg, conicParameterOrigin_z, neg_zero]

end FLT.Mazur.WeierstrassModificationX
