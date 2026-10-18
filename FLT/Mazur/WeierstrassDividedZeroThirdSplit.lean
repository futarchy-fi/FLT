/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroThirdFields

/-!
# Simultaneous third fields for the depth-zero chain

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
local notation "q" => arithmeticZeroThirdIntegralField hπ data H j hj u hu
local notation "e" => arithmeticZeroThirdField hπ data H j hj u hu

/-- The full relative initial error contributes its reciprocal nonpositive part. -/
def arithmeticZeroThirdInitialField (b : Bool) : R[T;T⁻¹] :=
  reciprocalField (nonpositivePart (q false b))

/-- The same last node receives an incoming and an outgoing correction. -/
def arithmeticZeroThirdLastField (b a : Bool) : R[T;T⁻¹] :=
  if a then reciprocalField (nonpositivePart (q true b)) else -positivePart (q false b)

/-- Both closing positive fields belong to one common terminal node. -/
def arithmeticZeroThirdTerminalField (b : Bool) : R[T;T⁻¹] := positivePart (q true b)

/-- The initial field extends across the initial node origin. -/
theorem arithmeticZeroThirdInitialField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticZeroThirdInitialField hπ data H j hj u hu b).coeff d = 0 :=
  reciprocal_nonpositive_coeff _ d hd

/-- Both last fields extend across their respective origins. -/
theorem arithmeticZeroThirdLastField_boundary (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticZeroThirdLastField hπ data H j hj u hu b a).coeff d = 0 := by
  cases a
  · exact LaurentReciprocalRelativeCorrection.neighborField_boundary _ d hd
  · exact reciprocal_nonpositive_coeff _ d hd

/-- Both terminal fields extend across the common terminal origin. -/
theorem arithmeticZeroThirdTerminalField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (arithmeticZeroThirdTerminalField hπ data H j hj u hu b).coeff d = 0 :=
  by rw [arithmeticZeroThirdTerminalField, positivePart_coeff, ite_eq_right (by omega)]

/-- The initial split specializes to the entire measured third relative field. -/
theorem arithmeticZeroThirdInitialField_spec (b : Bool) :
    correctionField R π 3 (arithmeticZeroThirdInitialField hπ data H j hj u hu b) =
      reciprocalField (nonpositivePart (e false b)) := by
  rw [arithmeticZeroThirdInitialField, correctionField_reciprocal,
    arithmeticZeroThirdIntegralField_spec]

/-- The last incoming correction cancels the positive relative initial error. -/
theorem arithmeticZeroThirdLastField_incoming_spec (b : Bool) :
    correctionField R π 3 (arithmeticZeroThirdLastField hπ data H j hj u hu b false) =
      -positivePart (e false b) := by
  change correctionField R π 3 (-positivePart (q false b)) = _
  rw [show ∀ z : R[T;T⁻¹], correctionField R π 3 (-z) = -correctionField R π 3 z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap (algebraMap R (Quotient R π 3))) z,
    correctionField_positive, arithmeticZeroThirdIntegralField_spec]

/-- The last outgoing correction is the reciprocal nonpositive closing error. -/
theorem arithmeticZeroThirdLastField_outgoing_spec (b : Bool) :
    correctionField R π 3 (arithmeticZeroThirdLastField hπ data H j hj u hu b true) =
      reciprocalField (nonpositivePart (e true b)) := by
  change correctionField R π 3 (reciprocalField (nonpositivePart (q true b))) = _
  rw [correctionField_reciprocal, arithmeticZeroThirdIntegralField_spec]

/-- The common terminal realizes both positive closing errors. -/
theorem arithmeticZeroThirdTerminalField_spec (b : Bool) :
    correctionField R π 3 (arithmeticZeroThirdTerminalField hπ data H j hj u hu b) =
      positivePart (e true b) := by
  rw [arithmeticZeroThirdTerminalField, correctionField_positive,
    arithmeticZeroThirdIntegralField_spec]

/-- The incoming linear term is kept without a zero-drift assumption. -/
theorem arithmeticZeroThirdLastField_linear (b : Bool) :
    (arithmeticZeroThirdLastField hπ data H j hj u hu b false).coeff 1 =
      -(q false b).coeff 1 := by
  change (-positivePart (q false b)).coeff 1 = _
  simp only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, positivePart_coeff,
    show (0 : ℤ) < 1 by omega, ↓reduceIte]

end FLT.Mazur.WeierstrassDividedDepth
