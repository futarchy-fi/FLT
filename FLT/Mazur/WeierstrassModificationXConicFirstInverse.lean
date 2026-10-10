/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicInverseCoordinates

/-!
# Both compositions of the first conic parameterization

The original conic neighborhood and the localized polynomial line are inverse
via their actual coordinate maps. Unit cancellation keeps these proofs at the
level of coordinates instead of expanding localization representatives.
-/

@[expose] public noncomputable section

open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R) (ha : IsUnit a)
local notation "P" => ConicParameterOpen c
local notation "O" => ConicFirstOpen a c
local notation "C₀" => ConicCoordinate a c
local notation "f" => conicParameterToFirst a c ha
local notation "g" => conicFirstToParameter a c ha
local notation "z" => conicFirstParameter a c
local notation "U" => algebraMap C₀ O (conicV a c + algebraMap R C₀ a)
local notation "T" => algebraMap C₀ O (conicT a c)
local notation "V" => algebraMap C₀ O (conicV a c)
local notation "A" => algebraMap R O a
local notation "C" => algebraMap R O c

/-- The forward map sends the polynomial parameter to the actual conic parameter. -/
theorem conicParameterToFirst_z : f (conicParameterZ c) = z := by
  rw [conicParameterZ, conicParameterToFirst_base, aeval_X]

/-- The inverse denominator recovers the opposite tangent factor. -/
theorem conicParameterToFirst_inv_mul : f (conicParameterInv c) * A = U := by
  have h := congrArg f (conicParameter_mul_inv c)
  simp only [map_mul, map_sub, map_one, map_pow, AlgHom.commutes,
    conicParameterToFirst_z] at h
  apply (conicFirstParameter_denominator_isUnit a c ha).mul_left_cancel
  calc (1 - C * z ^ 2) * (f (conicParameterInv c) * A) = A := by
        rw [← mul_assoc, h, one_mul]
    _ = (1 - C * z ^ 2) * U := (conicFirstParameter_denominator_mul a c).symm

/-- The forward image of the inverse incidence coordinate is the original t. -/
theorem conicParameterToFirst_inverseT : f (conicInverseT a c) = T := by
  rw [conicInverseT, map_mul, map_mul, AlgHom.commutes, conicParameterToFirst_z]
  calc A * z * f (conicParameterInv c) = z * (f (conicParameterInv c) * A) := by ring
    _ = T := by rw [conicParameterToFirst_inv_mul, conicFirstParameter_mul]

/-- The forward image of the inverse slope coordinate is the original v. -/
theorem conicParameterToFirst_inverseV : f (conicInverseV a c) = V := by
  have h := conicFirstParameter_denominator_mul a c
  have hu : U = V + A := by
    rw [map_add, ← IsScalarTower.algebraMap_apply R C₀ O]
  rw [conicInverseV, map_mul, map_mul, map_mul, map_pow, AlgHom.commutes,
    AlgHom.commutes, conicParameterToFirst_z]
  calc A * C * z ^ 2 * f (conicParameterInv c) =
      C * z ^ 2 * (f (conicParameterInv c) * A) := by ring
    _ = U - A := by rw [conicParameterToFirst_inv_mul, ← h]; ring
    _ = V := by rw [hu]; ring

/-- The inverse map sends the actual rational parameter back to the polynomial one. -/
theorem conicFirstToParameter_parameter : g z = conicParameterZ c := by
  have h := congrArg g (conicFirstParameter_mul a c)
  rw [map_mul, conicFirstToParameter_base, conicFirstToParameter_base,
    conicToParameter_t, map_add, conicToParameter_v, AlgHom.commutes] at h
  apply (conicInverseV_add_isUnit a c ha).mul_right_cancel
  calc g z * (conicInverseV a c + algebraMap R P a) = conicInverseT a c := h
    _ = conicParameterZ c * (conicInverseV a c + algebraMap R P a) := by
      rw [conicInverseV_add, conicInverseT]
      ring

/-- Composing the actual maps on the first conic neighborhood is the identity. -/
theorem conicParameterToFirst_comp : (f).comp g = AlgHom.id R O := by
  apply IsLocalization.algHom_ext (Submonoid.powers (conicV a c + algebraMap R C₀ a))
  apply conic_hom_ext a c
  · change f (g T) = T
    rw [conicFirstToParameter_base, conicToParameter_t, conicParameterToFirst_inverseT]
  · change f (g V) = V
    rw [conicFirstToParameter_base, conicToParameter_v, conicParameterToFirst_inverseV]

/-- Composing the actual maps on the parameter neighborhood is the identity. -/
theorem conicFirstToParameter_comp : (g).comp f = AlgHom.id R P := by
  apply IsLocalization.algHom_ext (Submonoid.powers (conicParameterPolynomial c))
  apply Polynomial.algHom_ext
  change g (f (conicParameterZ c)) = conicParameterZ c
  rw [conicParameterToFirst_z, conicFirstToParameter_parameter]

/-- The actual first conic neighborhood is an open of the affine parameter line. -/
def conicFirstParameterEquiv : P ≃ₐ[R] O :=
  AlgEquiv.ofAlgHom f g (conicParameterToFirst_comp a c ha) (conicFirstToParameter_comp a c ha)

/-- The equivalence uses the original forward parameter map. -/
theorem conicFirstParameterEquiv_toAlgHom :
    (conicFirstParameterEquiv a c ha).toAlgHom = f := rfl
/-- The inverse equivalence uses the constructed inverse coordinate map. -/
theorem conicFirstParameterEquiv_symm_toAlgHom :
    (conicFirstParameterEquiv a c ha).symm.toAlgHom = g := rfl

end FLT.Mazur.WeierstrassModificationX
