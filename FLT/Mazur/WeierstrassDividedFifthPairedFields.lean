/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthResidualFields

/-!
# Fifth fields for an arbitrary pair of incident full residuals

The outgoing positive and incoming negative reciprocal projections are selected
independently. This keeps the same whole-node factor on both incident edges.
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

/-- Two incident full residuals determine one pair of boundary-vanishing integral fields. -/
def arithmeticFifthPairedField (out inc : FourthResidualEdge) (b a : Bool) :
    R[T;T⁻¹] :=
  if a then positivePart (q out b)
  else -reciprocalField (nonpositivePart (q inc b))

local notation "P" => arithmeticFifthPairedField hπ data H j hj u hu

/-- Each branch field extends across its own node origin. -/
theorem arithmeticFifthPairedField_boundary (out inc : FourthResidualEdge)
    (b a : Bool) (d : ℤ) (hd : d ≤ 0) : (P out inc b a).coeff d = 0 := by
  cases a
  · change (-reciprocalField (nonpositivePart (q inc b))).coeff d = 0
    rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply,
      reciprocal_nonpositive_coeff _ d hd, neg_zero]
  · change (positivePart (q out b)).coeff d = 0
    rw [positivePart_coeff, ite_eq_right (by omega)]

/-- The complementary incoming field contributes no linear smoothing drift. -/
theorem arithmeticFifthPairedField_incoming_linear (out inc : FourthResidualEdge)
    (b : Bool) : (P out inc b false).coeff 1 = 0 := by
  simp only [arithmeticFifthPairedField, Bool.false_eq_true, ↓reduceIte,
    AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, reciprocalField_coeff,
    nonpositivePart_coeff]
  norm_num

/-- Both full integral fields carry fifth-order weight. -/
def arithmeticFifthPairedIntegralField (out inc : FourthResidualEdge) (b a : Bool) :
    R[T;T⁻¹] := higherCorrectionField R π 4 (P out inc b a)

/-- The outgoing field keeps every positive coefficient of the complete residual. -/
theorem arithmeticFifthPairedField_outgoing (out inc : FourthResidualEdge) (b : Bool) :
    correctionField R π 5 (P out inc b true) =
      positivePart (arithmeticFifthResidualField hπ data H j hj u hu out b) := by
  change correctionField R π 5 (positivePart _) = _
  rw [correctionField_positive, arithmeticFifthResidualIntegralField_spec]

/-- The incoming field keeps every complementary coefficient, with the reciprocal sign. -/
theorem arithmeticFifthPairedField_incoming (out inc : FourthResidualEdge) (b : Bool) :
    correctionField R π 5 (P out inc b false) =
      -reciprocalField (nonpositivePart
        (arithmeticFifthResidualField hπ data H j hj u hu inc b)) := by
  change correctionField R π 5 (-reciprocalField (nonpositivePart _)) = _
  rw [show ∀ z : R[T;T⁻¹], correctionField R π 5 (-z) = -correctionField R π 5 z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap
      (algebraMap R (Quotient R π 5))) z,
    correctionField_reciprocal, arithmeticFifthResidualIntegralField_spec]

end FLT.Mazur.WeierstrassDividedDepth
