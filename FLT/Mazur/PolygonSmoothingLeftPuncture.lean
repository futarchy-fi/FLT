/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingRing
public import FLT.Mazur.LaurentUnitPoints

/-!
# The punctured first branch of an arithmetic smoothing chart

Inverting x in R[x,y]/(xy-t) gives R[z,z⁻¹], with x = z and y = t/z.
The equivalence is over arbitrary coefficient rings and retains the parameter.
-/

@[expose] public noncomputable section

open scoped LaurentPolynomial

namespace FLT.Mazur.PolygonSmoothing

variable {R : Type*} [CommRing R]

/-- The actual localization of the smoothing chart away from its first coordinate. -/
abbrev LeftPuncture (t : R) := Localization.Away (leftCoordinate t)

/-- The invertible first coordinate in the punctured chart. -/
def leftPunctureUnit (t : R) : (LeftPuncture t)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (leftCoordinate t)).unit

/-- The unit retains the original localized coordinate. -/
@[simp] theorem leftPunctureUnit_val (t : R) :
    (leftPunctureUnit t).val = algebraMap (ChartRing t) _ (leftCoordinate t) :=
  IsUnit.unit_spec _

/-- The second localized coordinate is the parameter divided by the first. -/
theorem leftPuncture_right (t : R) :
    algebraMap (ChartRing t) (LeftPuncture t) (rightCoordinate t) =
      algebraMap R _ t * ↑(leftPunctureUnit t)⁻¹ := by
  apply (Units.mul_left_inj (leftPunctureUnit t)).mp
  rw [mul_assoc, Units.inv_mul, mul_one, leftPunctureUnit_val, ← map_mul,
    mul_comm (rightCoordinate t), coordinate_relation,
    ← IsScalarTower.algebraMap_apply R (ChartRing t) (LeftPuncture t)]

/-- The Laurent presentation of the original chart before localization. -/
def leftLaurentMap (t : R) : ChartRing t →ₐ[R] R[T;T⁻¹] :=
  evaluate t (LaurentPolynomial.T 1)
    (LaurentPolynomial.C t * LaurentPolynomial.T (-1)) (by
      rw [mul_left_comm, ← LaurentPolynomial.T_add]
      simp only [Int.reduceAdd, LaurentPolynomial.T_zero, mul_one]
      exact LaurentPolynomial.C_eq_algebraMap t)

/-- The first chart coordinate is the Laurent variable. -/
@[simp] theorem leftLaurentMap_left (t : R) :
    leftLaurentMap t (leftCoordinate t) = LaurentPolynomial.T 1 := evaluate_left ..

/-- The second chart coordinate is t times the inverse Laurent variable. -/
@[simp] theorem leftLaurentMap_right (t : R) :
    leftLaurentMap t (rightCoordinate t) =
      LaurentPolynomial.C t * LaurentPolynomial.T (-1) := evaluate_right ..

/-- Localization extends the Laurent presentation to the punctured chart. -/
def leftPunctureToLaurent (t : R) : LeftPuncture t →ₐ[R] R[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom (leftCoordinate t) (f := leftLaurentMap t) (by
    rw [leftLaurentMap_left]
    exact LaurentPolynomial.isUnit_T 1)

/-- The extended presentation agrees with the original chart map. -/
@[simp] theorem leftPunctureToLaurent_map (t : R) (a : ChartRing t) :
    leftPunctureToLaurent t (algebraMap (ChartRing t) _ a) = leftLaurentMap t a :=
  IsLocalization.Away.lift_eq (leftCoordinate t) (by
    change IsUnit (leftLaurentMap t (leftCoordinate t))
    rw [leftLaurentMap_left]
    exact LaurentPolynomial.isUnit_T 1) a

/-- Laurent evaluation at the actual localized first coordinate. -/
def laurentToLeftPuncture (t : R) : R[T;T⁻¹] →ₐ[R] LeftPuncture t :=
  LaurentUnitPoints.evalUnit (leftPunctureUnit t)

/-- The two explicit coordinate maps are inverse on the localization. -/
theorem laurentToLeftPuncture_comp (t : R) :
    (laurentToLeftPuncture t).comp (leftPunctureToLaurent t) = AlgHom.id R _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (leftCoordinate t))
  apply chartRing_hom_ext t
  · simp [Algebra.algHom, laurentToLeftPuncture]
  · change laurentToLeftPuncture t
      (leftPunctureToLaurent t (algebraMap (ChartRing t) _ (rightCoordinate t))) = _
    rw [leftPunctureToLaurent_map, leftLaurentMap_right, map_mul]
    simp [Algebra.algHom, laurentToLeftPuncture, leftPuncture_right]

/-- The two explicit coordinate maps are inverse on the Laurent algebra. -/
theorem leftPunctureToLaurent_comp (t : R) :
    (leftPunctureToLaurent t).comp (laurentToLeftPuncture t) = AlgHom.id R _ := by
  apply LaurentUnitPoints.pointsEquiv.injective
  apply Units.ext
  simp [LaurentUnitPoints.pointsEquiv, LaurentUnitPoints.pointUnit, laurentToLeftPuncture]

/-- The punctured first branch is the actual Laurent algebra over the coefficient ring. -/
def leftPunctureEquiv (t : R) : LeftPuncture t ≃ₐ[R] R[T;T⁻¹] :=
  AlgEquiv.ofAlgHom (leftPunctureToLaurent t) (laurentToLeftPuncture t)
    (leftPunctureToLaurent_comp t) (laurentToLeftPuncture_comp t)

end FLT.Mazur.PolygonSmoothing
