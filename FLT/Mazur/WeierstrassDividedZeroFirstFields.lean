/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthZeroFirstField
public import FLT.Mazur.LaurentReciprocalRelativeCorrection

/-!
# Simultaneous first fields at depth zero

The first retained node is the last node. Its incoming field cancels the positive
initial error; its outgoing field is zero since the closing edge is already
correct through layer four. Keep the incoming linear coefficient and its drift.
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
local notation "q" => arithmeticFourthZeroFirstIntegralField hπ data H j hj u hu

/-- The original initial node receives the reciprocal nonpositive relative field. -/
def arithmeticZeroFirstInitialField (b : Bool) : R[T;T⁻¹] :=
  LaurentReciprocalRelativeCorrection.initialField (q b)

/-- One last node receives its initial correction and a zero outgoing field. -/
def arithmeticZeroFirstLastField (b a : Bool) : R[T;T⁻¹] :=
  if a then 0 else LaurentReciprocalRelativeCorrection.neighborField (q b)

/-- The initial field extends across the original node origin. -/
theorem arithmeticZeroFirstInitialField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticZeroFirstInitialField hπ data H j hj u hu b).coeff d = 0 :=
  LaurentReciprocalRelativeCorrection.initialField_boundary _ d hd

/-- Both last-node fields extend across their respective node origins. -/
theorem arithmeticZeroFirstLastField_boundary (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticZeroFirstLastField hπ data H j hj u hu b a).coeff d = 0 := by
  cases a
  · exact LaurentReciprocalRelativeCorrection.neighborField_boundary _ d hd
  · rfl

/-- Specialization retains the complete complementary initial field. -/
theorem arithmeticZeroFirstInitialField_spec (b : Bool) :
    correctionField R π 1 (arithmeticZeroFirstInitialField hπ data H j hj u hu b) =
      reciprocalField (nonpositivePart (arithmeticFourthZeroFirstField hπ data H j hj u hu b)) := by
  rw [arithmeticZeroFirstInitialField, LaurentReciprocalRelativeCorrection.initialField,
    correctionField_reciprocal, arithmeticFourthZeroFirstIntegralField_spec]

/-- The last incoming field removes the entire positive initial error. -/
theorem arithmeticZeroFirstLastField_spec (b : Bool) :
    correctionField R π 1 (arithmeticZeroFirstLastField hπ data H j hj u hu b false) =
      -positivePart (arithmeticFourthZeroFirstField hπ data H j hj u hu b) := by
  change correctionField R π 1 (-positivePart (q b)) = _
  rw [show ∀ z : R[T;T⁻¹], correctionField R π 1 (-z) = -correctionField R π 1 z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap (algebraMap R (Quotient R π 1))) z,
    correctionField_positive, arithmeticFourthZeroFirstIntegralField_spec]

/-- The last incoming linear coefficient is retained without a zero-drift assumption. -/
theorem arithmeticZeroFirstLastField_linear (b : Bool) :
    (arithmeticZeroFirstLastField hπ data H j hj u hu b false).coeff 1 = -(q b).coeff 1 := by
  change (-positivePart (q b)).coeff 1 = _
  simp only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, positivePart_coeff,
    show (0 : ℤ) < 1 by omega, ↓reduceIte]

end FLT.Mazur.WeierstrassDividedDepth
