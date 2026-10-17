/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualIntegralLift
public import FLT.Mazur.PolygonArithmeticNodeCorrectionLift

/-!
# Compatible whole-node lifts of the actual retained residual corrections

The integral reciprocal fields lift both original retained corrections at
all arithmetic orders. Their linear coefficients vanish, so these particular
lifts have no smoothing drift. Their full quotient squares and first-order
identifications hold on whole nodes, including nilpotent terms.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "τ" => fun m ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "q" => arithmeticRetainedIntegralField hπ data H j hj u hu
local notation "s" => fun m b ↦ correctionSmoothing R π m (τ m) (q b)

/-- The retained correction lift has precisely the original smoothing at every order. -/
theorem arithmeticResidualRetainedLift_smoothing (m : ℕ) (b : Bool) : s m b = τ m := by
  simp only [correctionSmoothing, arithmeticRetainedIntegralField_linear,
    map_zero, mul_zero, add_zero, one_mul]

/-- The full original retained correction lifted to any arithmetic parameter order. -/
irreducible_def arithmeticResidualRetainedLift (m : ℕ) (b : Bool) :
    ChartRing (s m b) ≃ₐ[Quotient R π m] ChartRing (τ m) :=
  correctionNodeFactor R π m (τ m) (q b)

/-- Every arithmetic quotient transports the whole retained node lift. -/
theorem arithmeticResidualRetainedLift_restriction (m : ℕ) (b : Bool) :
    (ringMap (restriction R π m).toRingHom (τ (m + 1)) (τ m)
        (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)).comp
      (arithmeticResidualRetainedLift hπ data H j hj u hu (m + 1) b).toAlgHom.toRingHom =
    (arithmeticResidualRetainedLift hπ data H j hj u hu m b).toAlgHom.toRingHom.comp
      (ringMap (restriction R π m).toRingHom (s (m + 1) b) (s m b)
        (correctionSmoothing_restriction R π m _ _
          (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) (q b))) := by
  rw [arithmeticResidualRetainedLift_def, arithmeticResidualRetainedLift_def]
  exact correctionNodeFactor_restriction R π m _ _ _ _

/-- The entire first-order retained factor is the original residual correction. -/
theorem arithmeticResidualRetainedLift_first (b : Bool) :
    (arithmeticResidualRetainedLift hπ data H j hj u hu 1 b).toAlgHom.toRingHom =
      (arithmeticFirstResidualRetainedFactor hπ data H j hj u hu b).toAlgHom.toRingHom.comp
        (ringMap (RingHom.id _) (s 1 b) (τ 1)
          (arithmeticResidualRetainedLift_smoothing hπ data H j hj u hu 1 b)) := by
  rw [arithmeticResidualRetainedLift_def]
  have ht : parameter R π 1 * τ 1 = 0 := by
    rw [mul_comm]
    exact arithmeticFirstSmoothing_mul_parameter data H
  have h := correctionNodeFactor_first R π (τ 1) ht (q b)
  rw [arithmeticRetainedIntegralField_first] at h
  exact h

/-- The full outgoing higher-order coordinate retains every coefficient of the chosen lift. -/
theorem arithmeticResidualRetainedLift_left (m : ℕ) (b : Bool) :
    leftLaurentMap (τ m)
      (arithmeticResidualRetainedLift hπ data H j hj u hu m b (leftCoordinate (s m b))) =
        T 1 + C (parameter R π m) * correctionField R π m (q b) := by
  rw [arithmeticResidualRetainedLift_def, correctionNodeFactor_def]
  unfold correctionSmoothing
  rw [nilpotentShearEquiv_left]
  simp only [map_mul, map_add, map_one, AlgHom.commutes, leftLaurentMap_left]
  change T 1 * (1 + C (parameter R π m) * leftLaurentMap (τ m)
    (LaurentBoundaryCorrectionSplit.boundaryLift (τ m) (correctionField R π m (q b)))) = _
  rw [mul_add, mul_one, mul_left_comm, boundaryLift_value]
  exact correctionField_boundary R π m (q b)
    (arithmeticRetainedIntegralField_boundary hπ data H j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
