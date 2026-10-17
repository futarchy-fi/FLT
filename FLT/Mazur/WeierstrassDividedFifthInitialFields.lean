/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthResidualFields
public import FLT.Mazur.LaurentReciprocalRelativeCorrection

/-!
# Fifth fields for the depth-one initial boundary

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
local notation "q" => arithmeticFifthResidualIntegralField hπ data H j hj u hu

/-- The original initial chart receives the reciprocal nonpositive relative field. -/
def arithmeticFifthInitialField (b : Bool) : R[T;T⁻¹] :=
  LaurentReciprocalRelativeCorrection.initialField (q .initial b)

/-- At depth one the predecessor uses the full initial relative field on its right branch. -/
def arithmeticFifthInitialNeighborField (b a : Bool) : R[T;T⁻¹] :=
  if a then positivePart (q .initialIncoming b)
  else LaurentReciprocalRelativeCorrection.neighborField (q .initial b)

/-- The initial field extends across its actual full node boundary. -/
theorem arithmeticFifthInitialField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticFifthInitialField hπ data H j hj u hu b).coeff d = 0 :=
  LaurentReciprocalRelativeCorrection.initialField_boundary _ d hd

/-- Both fields of the depth-one predecessor extend across their own node origins. -/
theorem arithmeticFifthInitialNeighborField_boundary (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticFifthInitialNeighborField hπ data H j hj u hu b a).coeff d = 0 := by
  cases a
  · exact LaurentReciprocalRelativeCorrection.neighborField_boundary _ d hd
  · change (positivePart _).coeff d = 0
    rw [positivePart_coeff, ite_eq_right (by omega)]

/-- Lift the full initial field once, with fifth-order arithmetic weight. -/
def arithmeticFifthInitialIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 4 (arithmeticFifthInitialField hπ data H j hj u hu b)

/-- The depth-one predecessor's two full integral correction fields. -/
def arithmeticFifthInitialNeighborIntegralField (b a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 4 (arithmeticFifthInitialNeighborField hπ data H j hj u hu b a)

/-- The initial lift realizes the complete reciprocal nonpositive relative field. -/
theorem arithmeticFifthInitialField_spec (b : Bool) :
    correctionField R π 5 (arithmeticFifthInitialField hπ data H j hj u hu b) =
      reciprocalField (nonpositivePart (arithmeticFifthResidualField hπ data H j hj u hu
        .initial b)) := by
  rw [arithmeticFifthInitialField, LaurentReciprocalRelativeCorrection.initialField,
    correctionField_reciprocal,
    arithmeticFifthResidualIntegralField_spec]

/-- The other initial endpoint removes exactly the positive relative error. -/
theorem arithmeticFifthInitialNeighborField_incoming_spec (b : Bool) :
    correctionField R π 5 (arithmeticFifthInitialNeighborField hπ data H j hj u hu b false) =
      -positivePart (arithmeticFifthResidualField hπ data H j hj u hu .initial b) := by
  simp only [arithmeticFifthInitialNeighborField, Bool.false_eq_true, ↓reduceIte,
    LaurentReciprocalRelativeCorrection.neighborField]
  rw [show ∀ z : R[T;T⁻¹], correctionField R π 5 (-z) = -correctionField R π 5 z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap (algebraMap R (Quotient R π 5))) z,
    correctionField_positive, arithmeticFifthResidualIntegralField_spec]

/-- The outgoing neighbor field addresses its actual full fourth incoming residual. -/
theorem arithmeticFifthInitialNeighborField_outgoing (b : Bool) :
    arithmeticFifthInitialNeighborField hπ data H j hj u hu b true =
      positivePart (q .initialIncoming b) := rfl

/-- The depth-one last node shares its closing field with the same common terminal. -/
def arithmeticFifthInitialLastField (b a : Bool) : R[T;T⁻¹] :=
  if a then reciprocalField (nonpositivePart (q .closing b))
  else -reciprocalField (nonpositivePart (q .initialIncoming b))

/-- Both full depth-one last fields vanish at their node origins. -/
theorem arithmeticFifthInitialLastField_boundary (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticFifthInitialLastField hπ data H j hj u hu b a).coeff d = 0 := by
  cases a
  · change (-reciprocalField (nonpositivePart (q .initialIncoming b))).coeff d = 0
    rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply,
      reciprocal_nonpositive_coeff _ d hd, neg_zero]
  · exact reciprocal_nonpositive_coeff _ d hd

/-- The depth-one last factor has zero scalar drift on both branches. -/
theorem arithmeticFifthInitialLastField_linear (b a : Bool) :
    (arithmeticFifthInitialLastField hπ data H j hj u hu b a).coeff 1 = 0 := by
  cases a <;> simp only [arithmeticFifthInitialLastField, Bool.false_eq_true, ↓reduceIte,
    AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, reciprocalField_coeff,
    nonpositivePart_coeff] <;> norm_num

/-- Scale both last-node fields once at fifth order with the same fixed integral lifts. -/
def arithmeticFifthInitialLastIntegralField (b a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 4 (arithmeticFifthInitialLastField hπ data H j hj u hu b a)

end FLT.Mazur.WeierstrassDividedDepth
