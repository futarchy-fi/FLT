/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingFirstLaurentLifts

/-!
# Nonlinear first-order lifts still preserve the smoothing weight

Even arbitrary node-polynomial corrections divisible by a square-zero
parameter cannot repair incompatible closed branch weights. This extends
the constant-scaling obstruction to full nonlinear coordinate lifts.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonSmoothing
open LaurentPolynomial
variable {R : Type*} [CommRing R] (t : R)

/-- Scalar multiplication acts coefficientwise on the full outgoing restriction. -/
theorem leftLaurentMap_scalar_coeff (r : R) (z : ChartRing t) (k : ℤ) :
    (leftLaurentMap t (algebraMap R (ChartRing t) r * z)).coeff k =
      r * (leftLaurentMap t z).coeff k := by
  simp only [map_mul, AlgHom.commutes, ← C_eq_algebraMap, ← smul_eq_C_mul,
    AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]

/-- Constant original scalars are detected exactly by the outgoing constant coefficient. -/
theorem leftLaurentMap_scalar_constant (r : R) :
    (leftLaurentMap t (algebraMap R (ChartRing t) r)).coeff 0 = r := by
  simp only [AlgHom.commutes, ← C_eq_algebraMap, ← single_eq_C,
    AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

/-- First-order corrections through the left coordinate have zero constant coefficient. -/
theorem squareZero_left_correction_constant (ht : t ^ 2 = 0) (z : ChartRing t) :
    (leftLaurentMap t (algebraMap R (ChartRing t) t * (leftCoordinate t * z))).coeff 0 =
      0 := by
  rw [leftLaurentMap_scalar_coeff, map_mul, leftLaurentMap_left]
  simp only [T, AddMonoidAlgebra.coeff_single_mul_apply, neg_add_eq_sub,
    zero_sub, one_mul]
  exact parameter_leftLaurentMap_negative t ht z (-1) (by decide)

/-- First-order corrections through the right coordinate also have zero constant coefficient. -/
theorem squareZero_right_correction_constant (ht : t ^ 2 = 0) (z : ChartRing t) :
    (leftLaurentMap t (algebraMap R (ChartRing t) t * (rightCoordinate t * z))).coeff 0 =
      0 := by
  rw [leftLaurentMap_scalar_coeff, map_mul, leftLaurentMap_right, ← single_eq_C_mul_T]
  simp only [AddMonoidAlgebra.coeff_single_mul_apply, neg_neg,
    ← mul_assoc, ← pow_two, ht, zero_mul]

/-- Arbitrary parameter-divisible coordinate corrections cannot alter the first smoothing weight. -/
theorem squareZero_lift_weight_constraint (ht : t ^ 2 = 0)
    (f : ChartRing t →ₐ[R] ChartRing t) (a b : R) (U V : ChartRing t)
    (hx : f (leftCoordinate t) = algebraMap R _ a * leftCoordinate t + algebraMap R _ t * U)
    (hy : f (rightCoordinate t) = algebraMap R _ b * rightCoordinate t + algebraMap R _ t * V) :
    a * b * t = t := by
  have he := congrArg f (coordinate_relation t)
  rw [map_mul, AlgHom.commutes, hx, hy] at he
  have ht' : (algebraMap R (ChartRing t) t) ^ 2 = 0 := by
    rw [← map_pow, ht, map_zero]
  have hp :
      (algebraMap R (ChartRing t) a * leftCoordinate t + algebraMap R _ t * U) *
        (algebraMap R _ b * rightCoordinate t + algebraMap R _ t * V) =
      algebraMap R _ (a * b * t) +
        algebraMap R _ t * (leftCoordinate t * (algebraMap R _ a * V)) +
        algebraMap R _ t * (rightCoordinate t * (algebraMap R _ b * U)) := by
    calc
      _ = (algebraMap R _ a * algebraMap R _ b) *
          (leftCoordinate t * rightCoordinate t) +
          algebraMap R _ t * (leftCoordinate t * (algebraMap R _ a * V)) +
          algebraMap R _ t * (rightCoordinate t * (algebraMap R _ b * U)) +
          (algebraMap R _ t) ^ 2 * (U * V) := by ring
      _ = _ := by rw [coordinate_relation, ht', zero_mul, add_zero, ← map_mul, ← map_mul]
  rw [hp] at he
  have hc := congrArg (fun z : ChartRing t ↦ (leftLaurentMap t z).coeff 0) he
  simpa only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    leftLaurentMap_scalar_constant, squareZero_left_correction_constant t ht,
    squareZero_right_correction_constant t ht, add_zero] using hc

end FLT.Mazur.PolygonSmoothing
