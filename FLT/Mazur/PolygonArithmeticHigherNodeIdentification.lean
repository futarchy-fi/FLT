/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticHigherCorrectionField
public import FLT.Mazur.LaurentBoundaryCorrectionScalar

/-!
# Whole-node identification of higher corrections

Scaling an integral field scales its entire node polynomial. On a layer
annihilating the smoothing, the compensating inverse fixes the opposite
coordinate and the full higher correction recovers the square-zero shear.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentBoundaryCorrectionSplit
open LaurentPolynomial PolygonSmoothing

/-- Multiplication by a coefficient scales the entire node polynomial. -/
theorem boundaryLift_C_mul {S : Type*} [CommRing S] (t c : S) (q : S[T;T⁻¹]) :
    boundaryLift t (C c * q) = algebraMap S (ChartRing t) c * boundaryLift t q := by
  rw [← smul_eq_C_mul, boundaryLift_smul]
  exact Algebra.smul_def c (boundaryLift t q)

end FLT.Mazur.LaurentBoundaryCorrectionSplit

namespace FLT.Mazur.PolygonArithmeticStages
open LaurentPolynomial PolygonSmoothing LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R) (m r : ℕ)
local notation "Q" => Quotient R π m
local notation "a" => parameter R π m
local notation "e" => a ^ (r + 1)

/-- The complete boundary polynomial has the intended higher scalar weight. -/
theorem higherCorrection_boundary_weight (t : Q) (q : R[T;T⁻¹]) :
    algebraMap Q (ChartRing t) a *
        boundaryLift t (correctionField R π m (higherCorrectionField R π r q)) =
      algebraMap Q (ChartRing t) e * boundaryLift t (correctionField R π m q) := by
  rw [correctionField_higher, boundaryLift_C_mul, ← mul_assoc, ← map_mul, ← pow_succ']

/-- The complete linear coefficient has the same higher scalar weight. -/
theorem higherCorrection_linear_weight (q : R[T;T⁻¹]) :
    a * algebraMap R Q ((higherCorrectionField R π r q).coeff 1) =
      e * (correctionField R π m q).coeff 1 := by
  rw [higherCorrectionField_coeff, map_mul, map_pow, correctionField_coeff]
  change a * (a ^ r * _) = _
  rw [← mul_assoc, ← pow_succ']

/-- The changed smoothing is equal to the input on an annihilated higher layer. -/
theorem correctionSmoothing_higher_eq (t : Q) (ht : e * t = 0) (q : R[T;T⁻¹]) :
    correctionSmoothing R π m t (higherCorrectionField R π r q) = t := by
  rw [correctionSmoothing_higher]
  exact nilpotentShear_parameter_eq t e ht _

/-- Every coordinate of the higher node lift agrees with its normalized square-zero shear. -/
theorem correctionNodeFactor_higher_eq (t : Q) (ht : e * t = 0) (q : R[T;T⁻¹]) :
    (correctionNodeFactor R π m t (higherCorrectionField R π r q)).toAlgHom.toRingHom =
      (squareZeroShear t e ht (boundaryLift t (correctionField R π m q))).toRingHom.comp
        (ringMap (RingHom.id Q) (correctionSmoothing R π m t
          (higherCorrectionField R π r q)) t (correctionSmoothing_higher_eq R π m r t ht q)) := by
  have hw := higherCorrection_boundary_weight R π m r t q
  have hc := higherCorrection_linear_weight R π m r q
  have hp : algebraMap Q (ChartRing t) a * rightCoordinate t *
      boundaryLift t (correctionField R π m (higherCorrectionField R π r q)) =
      algebraMap Q (ChartRing t) a * rightCoordinate t *
        algebraMap R (ChartRing t) ((higherCorrectionField R π r q).coeff 1) := by
    calc
      _ = rightCoordinate t * (algebraMap Q (ChartRing t) e *
          boundaryLift t (correctionField R π m q)) := by rw [← hw]; ring
      _ = algebraMap Q (ChartRing t) e * rightCoordinate t *
          algebraMap Q (ChartRing t) ((correctionField R π m q).coeff 1) := by
        rw [← mul_assoc, mul_comm (rightCoordinate t),
          boundaryLift_weighted_right t e ht]
      _ = _ := by
        have hh := congrArg (algebraMap Q (ChartRing t)) hc
        rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply R Q (ChartRing t)] at hh
        linear_combination rightCoordinate t * hh.symm
  rw [correctionNodeFactor_def]
  unfold correctionSmoothing
  apply chartRing_ringHom_ext
  · intro z
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, ringMap_scalar, RingHom.id_apply]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgEquiv.coe_toAlgHom, nilpotentShearEquiv_left, ringMap_left, squareZeroShear_left]
    rw [hw]
    ring
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgEquiv.coe_toAlgHom, ringMap_right, squareZeroShear_right]
    apply nilpotentShearEquiv_right_fixed
    simpa only [IsScalarTower.algebraMap_apply R Q (ChartRing t)] using hp

end FLT.Mazur.PolygonArithmeticStages
