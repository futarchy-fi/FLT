/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthJointFields
public import FLT.Mazur.LaurentReciprocalRelativeCorrection

/-!
# Fourth fields for the depth-two initial boundary

The full initial relative residual supplies its own complementary fields.
The earlier neighbor keeps its existing outgoing field and receives the negative
positive part at its right puncture. Both fields retain integral lifts.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "q" => arithmeticFourthResidualIntegralField hπ data H j hj u hu

/-- The original initial chart receives the reciprocal nonpositive relative field. -/
def arithmeticFourthShallowField (b : Bool) : R[T;T⁻¹] :=
  LaurentReciprocalRelativeCorrection.initialField (q .earlierDirect b)

/-- At depth two the earlier neighbor uses the full initial relative field on its right branch. -/
def arithmeticFourthShallowNeighborField (b a : Bool) : R[T;T⁻¹] :=
  if a then arithmeticFourthEarlierField hπ data H j hj u hu b
  else LaurentReciprocalRelativeCorrection.neighborField (q .earlierDirect b)

/-- The initial field extends across its actual full node boundary. -/
theorem arithmeticFourthShallowField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticFourthShallowField hπ data H j hj u hu b).coeff d = 0 :=
  LaurentReciprocalRelativeCorrection.initialField_boundary _ d hd

/-- Both fields of the depth-two earlier neighbor extend across their own node origins. -/
theorem arithmeticFourthShallowNeighborField_boundary (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticFourthShallowNeighborField hπ data H j hj u hu b a).coeff d = 0 := by
  cases a
  · exact LaurentReciprocalRelativeCorrection.neighborField_boundary _ d hd
  · change (positivePart _).coeff d = 0
    rw [positivePart_coeff, ite_eq_right (by omega)]

/-- Lift the full initial field once, with fourth-order arithmetic weight. -/
def arithmeticFourthShallowIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 3 (arithmeticFourthShallowField hπ data H j hj u hu b)

/-- The depth-two earlier neighbor's two full integral correction fields. -/
def arithmeticFourthShallowNeighborIntegralField (b a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 3 (arithmeticFourthShallowNeighborField hπ data H j hj u hu b a)

/-- The initial lift realizes the complete reciprocal nonpositive relative field. -/
theorem arithmeticFourthShallowField_spec (b : Bool) :
    correctionField R π 4 (arithmeticFourthShallowField hπ data H j hj u hu b) =
      reciprocalField (nonpositivePart (arithmeticFourthResidualField hπ data H j hj u hu
        .earlierDirect b)) := by
  rw [arithmeticFourthShallowField, LaurentReciprocalRelativeCorrection.initialField,
    correctionField_reciprocal,
    arithmeticFourthResidualIntegralField_spec]

/-- The other initial endpoint removes exactly the positive relative error. -/
theorem arithmeticFourthShallowNeighborField_incoming_spec (b : Bool) :
    correctionField R π 4 (arithmeticFourthShallowNeighborField hπ data H j hj u hu b false) =
      -positivePart (arithmeticFourthResidualField hπ data H j hj u hu .earlierDirect b) := by
  simp only [arithmeticFourthShallowNeighborField, Bool.false_eq_true, ↓reduceIte,
    LaurentReciprocalRelativeCorrection.neighborField]
  rw [show ∀ z : R[T;T⁻¹], correctionField R π 4 (-z) = -correctionField R π 4 z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap (algebraMap R (Quotient R π 4))) z,
    correctionField_positive, arithmeticFourthResidualIntegralField_spec]

/-- Its outgoing field is unchanged, so the interior incoming cancellation still applies. -/
theorem arithmeticFourthShallowNeighborField_outgoing (b : Bool) :
    arithmeticFourthShallowNeighborField hπ data H j hj u hu b true =
      arithmeticFourthEarlierField hπ data H j hj u hu b := rfl

end FLT.Mazur.WeierstrassDividedDepth
