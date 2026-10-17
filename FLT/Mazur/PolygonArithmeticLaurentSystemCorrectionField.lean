/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticLaurentSystemRestriction
public import FLT.Mazur.PolygonArithmeticHigherCorrectionField
public import FLT.Mazur.LaurentSquareZeroAutomorphism

/-!
# Construct the next integral field from a full compatible residual

An identity at stage r gives a finite Laurent quotient of the coordinate
error at stage r+1. Lift that entire quotient once to the original ring;
its scaled field defines actual full node corrections at every later order.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open LaurentPolynomial PolygonScalingNaturality
variable {R : Type*} [CommRing R] {π : R}
variable (a : (m : ℕ) → (Quotient R π m)[T;T⁻¹] →ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹])
  (ha : ∀ m, (coeffMap (restriction R π m).toRingHom).comp (a (m + 1)).toRingHom =
    (a m).toRingHom.comp (coeffMap (restriction R π m).toRingHom))
  (r : ℕ) (hr : a r = AlgHom.id (Quotient R π r) _)

/-- The full finite coordinate error divided by its proved parameter power. -/
def laurentSystemNextField : (Quotient R π (r + 1))[T;T⁻¹] :=
  (laurentSystem_error_dvd a ha (Nat.le_succ r) hr (T 1)).choose

/-- The chosen quotient recovers every term of the actual next coordinate error. -/
theorem laurentSystemNextField_coordinate :
    a (r + 1) (T 1) = T 1 + C (parameter R π (r + 1) ^ (r + 1)) *
      laurentSystemNextField a ha r hr := by
  have h := (laurentSystem_error_dvd a ha (Nat.le_succ r) hr (T 1)).choose_spec
  change a (r + 1) (T 1) - T 1 =
    C (parameter R π (r + 1) ^ (r + 1)) * laurentSystemNextField a ha r hr at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

/-- The next-layer parameter power is square-zero in its actual arithmetic coefficient ring. -/
theorem nextCorrectionParameter_square (R : Type*) [CommRing R] (π : R) (r : ℕ) :
    (parameter R π (r + 1) ^ (r + 1)) ^ 2 = 0 := by
  rw [← pow_mul, show (r + 1) * 2 = (r + 1 + 1) + r by omega, pow_add,
    parameter_pow, zero_mul]

/-- The complete next-layer residual is the constructed square-zero substitution. -/
theorem laurentSystemNextField_subst :
    a (r + 1) = LaurentSquareZeroAutomorphism.subst
      (parameter R π (r + 1) ^ (r + 1)) (nextCorrectionParameter_square R π r)
      (laurentSystemNextField a ha r hr) :=
  LaurentSquareZeroAutomorphism.eq_subst _ _ _ _
    (laurentSystemNextField_coordinate a ha r hr)

/-- One integral lift supplies compatible correction fields at every arithmetic order. -/
def laurentSystemNextIntegralField : R[T;T⁻¹] :=
  integralCorrectionLift R π (r + 1) (laurentSystemNextField a ha r hr)

/-- The integral lift retains the whole prescribed finite field at its defining layer. -/
theorem laurentSystemNextIntegralField_spec :
    correctionField R π (r + 1) (laurentSystemNextIntegralField a ha r hr) =
      laurentSystemNextField a ha r hr := integralCorrectionLift_spec R π _ _

/-- Its specialization realizes the actual full coordinate error at the next stage. -/
theorem laurentSystemNextIntegralField_coordinate :
    a (r + 1) (T 1) = T 1 + C (parameter R π (r + 1) ^ (r + 1)) *
      correctionField R π (r + 1) (laurentSystemNextIntegralField a ha r hr) := by
  rw [laurentSystemNextIntegralField_spec]
  exact laurentSystemNextField_coordinate a ha r hr

/-- Scaling the one integral lift produces the field accepted by the full node constructions. -/
def laurentSystemNextCorrectionField : R[T;T⁻¹] :=
  higherCorrectionField R π r (laurentSystemNextIntegralField a ha r hr)

/-- The scaled field recovers the entire next coordinate, in the existing correction convention. -/
theorem laurentSystemNextCorrectionField_coordinate :
    a (r + 1) (T 1) = T 1 + C (parameter R π (r + 1)) *
      correctionField R π (r + 1) (laurentSystemNextCorrectionField a ha r hr) := by
  rw [laurentSystemNextCorrectionField, correctionField_higher, ← mul_assoc,
    ← map_mul, ← pow_succ']
  exact laurentSystemNextIntegralField_coordinate a ha r hr

end FLT.Mazur.PolygonArithmeticStages
