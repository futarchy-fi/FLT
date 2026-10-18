/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSecondFields

/-!
# Simultaneous second fields for the depth-zero chain

The unique last node receives both measured errors. Its incoming linear term
is retained; the common terminal receives the two positive closing fields.
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
local notation "q" => arithmeticZeroSecondIntegralField hπ data H j hj u hu
local notation "e" => arithmeticZeroSecondField hπ data H j hj u hu

/-- The full relative initial error contributes its reciprocal nonpositive part. -/
def arithmeticZeroSecondInitialField (b : Bool) : R[T;T⁻¹] :=
  reciprocalField (nonpositivePart (q false b))

/-- The same last node receives an incoming and an outgoing correction. -/
def arithmeticZeroSecondLastField (b a : Bool) : R[T;T⁻¹] :=
  if a then reciprocalField (nonpositivePart (q true b)) else -positivePart (q false b)

/-- Both closing positive fields belong to one common terminal node. -/
def arithmeticZeroSecondTerminalField (b : Bool) : R[T;T⁻¹] := positivePart (q true b)

/-- The initial field extends across the initial node origin. -/
theorem arithmeticZeroSecondInitialField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticZeroSecondInitialField hπ data H j hj u hu b).coeff d = 0 :=
  reciprocal_nonpositive_coeff _ d hd

/-- Both last fields extend across their respective origins. -/
theorem arithmeticZeroSecondLastField_boundary (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticZeroSecondLastField hπ data H j hj u hu b a).coeff d = 0 := by
  cases a
  · exact LaurentReciprocalRelativeCorrection.neighborField_boundary _ d hd
  · exact reciprocal_nonpositive_coeff _ d hd

/-- Both terminal fields extend across the common terminal origin. -/
theorem arithmeticZeroSecondTerminalField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticZeroSecondTerminalField hπ data H j hj u hu b).coeff d = 0 :=
  by rw [arithmeticZeroSecondTerminalField, positivePart_coeff, ite_eq_right (by omega)]

/-- The initial split specializes to the entire measured second relative field. -/
theorem arithmeticZeroSecondInitialField_spec (b : Bool) :
    correctionField R π 2 (arithmeticZeroSecondInitialField hπ data H j hj u hu b) =
      reciprocalField (nonpositivePart (e false b)) := by
  rw [arithmeticZeroSecondInitialField, correctionField_reciprocal,
    arithmeticZeroSecondIntegralField_spec]

/-- The last incoming correction cancels the positive relative initial error. -/
theorem arithmeticZeroSecondLastField_incoming_spec (b : Bool) :
    correctionField R π 2 (arithmeticZeroSecondLastField hπ data H j hj u hu b false) =
      -positivePart (e false b) := by
  change correctionField R π 2 (-positivePart (q false b)) = _
  rw [show ∀ z : R[T;T⁻¹], correctionField R π 2 (-z) = -correctionField R π 2 z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap (algebraMap R (Quotient R π 2))) z,
    correctionField_positive, arithmeticZeroSecondIntegralField_spec]

/-- The last outgoing correction is the reciprocal nonpositive closing error. -/
theorem arithmeticZeroSecondLastField_outgoing_spec (b : Bool) :
    correctionField R π 2 (arithmeticZeroSecondLastField hπ data H j hj u hu b true) =
      reciprocalField (nonpositivePart (e true b)) := by
  change correctionField R π 2 (reciprocalField (nonpositivePart (q true b))) = _
  rw [correctionField_reciprocal, arithmeticZeroSecondIntegralField_spec]

/-- The common terminal realizes both positive closing errors. -/
theorem arithmeticZeroSecondTerminalField_spec (b : Bool) :
    correctionField R π 2 (arithmeticZeroSecondTerminalField hπ data H j hj u hu b) =
      positivePart (e true b) := by
  rw [arithmeticZeroSecondTerminalField, correctionField_positive,
    arithmeticZeroSecondIntegralField_spec]

/-- The incoming linear term is kept without a zero-drift assumption. -/
theorem arithmeticZeroSecondLastField_linear (b : Bool) :
    (arithmeticZeroSecondLastField hπ data H j hj u hu b false).coeff 1 =
      -(q false b).coeff 1 := by
  change (-positivePart (q false b)).coeff 1 = _
  simp only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, positivePart_coeff,
    show (0 : ℤ) < 1 by omega, ↓reduceIte]

end FLT.Mazur.WeierstrassDividedDepth
