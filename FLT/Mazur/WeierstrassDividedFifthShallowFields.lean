/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowJointFields
public import FLT.Mazur.LaurentReciprocalRelativeCorrection

/-!
# Fifth fields for the depth-two initial boundary

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
local notation "q" => arithmeticFifthResidualIntegralField hπ data H j hj u hu

/-- The original initial chart receives the reciprocal nonpositive relative field. -/
def arithmeticFifthShallowField (b : Bool) : R[T;T⁻¹] :=
  LaurentReciprocalRelativeCorrection.initialField (q .shallow b)

/-- At depth two the earlier neighbor uses the full initial relative field on its right branch. -/
def arithmeticFifthShallowNeighborField (b a : Bool) : R[T;T⁻¹] :=
  if a then arithmeticFifthShallowEarlierField hπ data H j hj u hu b
  else LaurentReciprocalRelativeCorrection.neighborField (q .shallow b)

/-- The initial field extends across its actual full node boundary. -/
theorem arithmeticFifthShallowField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticFifthShallowField hπ data H j hj u hu b).coeff d = 0 :=
  LaurentReciprocalRelativeCorrection.initialField_boundary _ d hd

/-- Both fields of the depth-two earlier neighbor extend across their own node origins. -/
theorem arithmeticFifthShallowNeighborField_boundary (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticFifthShallowNeighborField hπ data H j hj u hu b a).coeff d = 0 := by
  cases a
  · exact LaurentReciprocalRelativeCorrection.neighborField_boundary _ d hd
  · change (positivePart _).coeff d = 0
    rw [positivePart_coeff, ite_eq_right (by omega)]

/-- Lift the full initial field once, with fifth-order arithmetic weight. -/
def arithmeticFifthShallowIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 4 (arithmeticFifthShallowField hπ data H j hj u hu b)

/-- The depth-two earlier neighbor's two full integral correction fields. -/
def arithmeticFifthShallowNeighborIntegralField (b a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 4 (arithmeticFifthShallowNeighborField hπ data H j hj u hu b a)

/-- The initial lift realizes the complete reciprocal nonpositive relative field. -/
theorem arithmeticFifthShallowField_spec (b : Bool) :
    correctionField R π 5 (arithmeticFifthShallowField hπ data H j hj u hu b) =
      reciprocalField (nonpositivePart (arithmeticFifthResidualField hπ data H j hj u hu
        .shallow b)) := by
  rw [arithmeticFifthShallowField, LaurentReciprocalRelativeCorrection.initialField,
    correctionField_reciprocal,
    arithmeticFifthResidualIntegralField_spec]

/-- The other initial endpoint removes exactly the positive relative error. -/
theorem arithmeticFifthShallowNeighborField_incoming_spec (b : Bool) :
    correctionField R π 5 (arithmeticFifthShallowNeighborField hπ data H j hj u hu b false) =
      -positivePart (arithmeticFifthResidualField hπ data H j hj u hu .shallow b) := by
  simp only [arithmeticFifthShallowNeighborField, Bool.false_eq_true, ↓reduceIte,
    LaurentReciprocalRelativeCorrection.neighborField]
  rw [show ∀ z : R[T;T⁻¹], correctionField R π 5 (-z) = -correctionField R π 5 z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap (algebraMap R (Quotient R π 5))) z,
    correctionField_positive, arithmeticFifthResidualIntegralField_spec]

/-- Its outgoing field is unchanged, so the interior incoming cancellation still applies. -/
theorem arithmeticFifthShallowNeighborField_outgoing (b : Bool) :
    arithmeticFifthShallowNeighborField hπ data H j hj u hu b true =
      arithmeticFifthShallowEarlierField hπ data H j hj u hu b := rfl

end FLT.Mazur.WeierstrassDividedDepth
