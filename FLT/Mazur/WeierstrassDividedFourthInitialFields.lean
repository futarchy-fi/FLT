/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthJointFields
public import FLT.Mazur.LaurentReciprocalRelativeCorrection

/-!
# Fourth fields for the depth-one initial boundary

The full initial relative residual supplies its own complementary fields.
The predecessor keeps its existing outgoing field and receives the negative
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
def arithmeticFourthInitialField (b : Bool) : R[T;T⁻¹] :=
  LaurentReciprocalRelativeCorrection.initialField (q .initial b)

/-- At depth one the predecessor uses the full initial relative field on its right branch. -/
def arithmeticFourthInitialNeighborField (b a : Bool) : R[T;T⁻¹] :=
  if a then arithmeticFourthPrecedingField hπ data H j hj u hu b true
  else LaurentReciprocalRelativeCorrection.neighborField (q .initial b)

/-- The initial field extends across its actual full node boundary. -/
theorem arithmeticFourthInitialField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticFourthInitialField hπ data H j hj u hu b).coeff d = 0 :=
  LaurentReciprocalRelativeCorrection.initialField_boundary _ d hd

/-- Both fields of the depth-one predecessor extend across their own node origins. -/
theorem arithmeticFourthInitialNeighborField_boundary (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticFourthInitialNeighborField hπ data H j hj u hu b a).coeff d = 0 := by
  cases a
  · exact LaurentReciprocalRelativeCorrection.neighborField_boundary _ d hd
  · exact arithmeticFourthPrecedingField_boundary hπ data H j hj u hu b true d hd

/-- Lift the full initial field once, with fourth-order arithmetic weight. -/
def arithmeticFourthInitialIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 3 (arithmeticFourthInitialField hπ data H j hj u hu b)

/-- The depth-one predecessor's two full integral correction fields. -/
def arithmeticFourthInitialNeighborIntegralField (b a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 3 (arithmeticFourthInitialNeighborField hπ data H j hj u hu b a)

/-- The initial lift realizes the complete reciprocal nonpositive relative field. -/
theorem arithmeticFourthInitialField_spec (b : Bool) :
    correctionField R π 4 (arithmeticFourthInitialField hπ data H j hj u hu b) =
      reciprocalField (nonpositivePart (arithmeticFourthResidualField hπ data H j hj u hu
        .initial b)) := by
  rw [arithmeticFourthInitialField, LaurentReciprocalRelativeCorrection.initialField,
    correctionField_reciprocal,
    arithmeticFourthResidualIntegralField_spec]

/-- The other initial endpoint removes exactly the positive relative error. -/
theorem arithmeticFourthInitialNeighborField_incoming_spec (b : Bool) :
    correctionField R π 4 (arithmeticFourthInitialNeighborField hπ data H j hj u hu b false) =
      -positivePart (arithmeticFourthResidualField hπ data H j hj u hu .initial b) := by
  simp only [arithmeticFourthInitialNeighborField, Bool.false_eq_true, ↓reduceIte,
    LaurentReciprocalRelativeCorrection.neighborField]
  rw [show ∀ z : R[T;T⁻¹], correctionField R π 4 (-z) = -correctionField R π 4 z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap (algebraMap R (Quotient R π 4))) z,
    correctionField_positive, arithmeticFourthResidualIntegralField_spec]

/-- Its outgoing field is unchanged, so the interior incoming cancellation still applies. -/
theorem arithmeticFourthInitialNeighborField_outgoing (b : Bool) :
    arithmeticFourthInitialNeighborField hπ data H j hj u hu b true =
      arithmeticFourthPrecedingField hπ data H j hj u hu b true := rfl

end FLT.Mazur.WeierstrassDividedDepth
