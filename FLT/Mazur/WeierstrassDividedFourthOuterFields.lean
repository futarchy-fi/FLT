/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthJointFields

/-!
# Simultaneous fourth fields on the further retained incoming edge

The earlier node keeps its outgoing preceding field and receives the
complementary reciprocal incoming field. Its farther retained neighbor receives
the remaining positive field. The original initial neighbor needs a separate base comparison.
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

/-- Both incident fields of the earlier retained node are chosen from their full residuals. -/
def arithmeticFourthOuterField (b a : Bool) : R[T;T⁻¹] :=
  if a then arithmeticFourthEarlierField hπ data H j hj u hu b
  else -reciprocalField (nonpositivePart (q .earlierIncoming b))

/-- The farther retained neighbor receives the positive incoming field. -/
def arithmeticFourthFartherField (b : Bool) : R[T;T⁻¹] :=
  positivePart (q .earlierIncoming b)

/-- Both earlier-node fields extend over their respective full node origins. -/
theorem arithmeticFourthOuterField_boundary (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticFourthOuterField hπ data H j hj u hu b a).coeff d = 0 := by
  cases a
  · change (-reciprocalField (nonpositivePart (q .earlierIncoming b))).coeff d = 0
    rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply,
      reciprocal_nonpositive_coeff _ d hd, neg_zero]
  · change (positivePart (q .preceding b)).coeff d = 0
    rw [positivePart_coeff, ite_eq_right (by omega)]

/-- The farther field also extends across its own full node origin. -/
theorem arithmeticFourthFartherField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticFourthFartherField hπ data H j hj u hu b).coeff d = 0 := by
  change (positivePart _).coeff d = 0
  rw [positivePart_coeff, ite_eq_right (by omega)]

/-- The earlier node's two fixed integral lifts have fourth-order weight. -/
def arithmeticFourthOuterIntegralField (b a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 3 (arithmeticFourthOuterField hπ data H j hj u hu b a)

/-- The farther retained neighbor's fixed integral lift has the same fourth-order weight. -/
def arithmeticFourthFartherIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 3 (arithmeticFourthFartherField hπ data H j hj u hu b)

/-- The earlier incoming lift specializes to the full complementary reciprocal field. -/
theorem arithmeticFourthOuterField_incoming_spec (b : Bool) :
    correctionField R π 4 (arithmeticFourthOuterField hπ data H j hj u hu b false) =
      -reciprocalField (nonpositivePart
        (arithmeticFourthResidualField hπ data H j hj u hu .earlierIncoming b)) := by
  simp only [arithmeticFourthOuterField, Bool.false_eq_true, ↓reduceIte]
  rw [show ∀ z : R[T;T⁻¹], correctionField R π 4 (-z) = -correctionField R π 4 z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap (algebraMap R (Quotient R π 4))) z,
    correctionField_reciprocal, arithmeticFourthResidualIntegralField_spec]

/-- The farther lift specializes to the full positive incoming field. -/
theorem arithmeticFourthFartherField_spec (b : Bool) :
    correctionField R π 4 (arithmeticFourthFartherField hπ data H j hj u hu b) =
      positivePart (arithmeticFourthResidualField hπ data H j hj u hu .earlierIncoming b) := by
  rw [arithmeticFourthFartherField, correctionField_positive,
    arithmeticFourthResidualIntegralField_spec]

end FLT.Mazur.WeierstrassDividedDepth
