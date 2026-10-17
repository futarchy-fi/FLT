/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthResidualFields

/-!
# Simultaneous fourth-layer inputs on the affected full nodes

The last node and its predecessor each receive two fields. The predecessor
keeps its positive outgoing field and negative reciprocal incoming field;
the next earlier node receives the remaining positive incoming field.
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

/-- The shared last retained node receives the two complementary fields. -/
def arithmeticFourthLastField (b a : Bool) : R[T;T⁻¹] :=
  if a then reciprocalField (nonpositivePart (q .closing b))
  else -reciprocalField (nonpositivePart (q .incoming b))

/-- The already corrected predecessor receives both remaining incident fields. -/
def arithmeticFourthPrecedingField (b a : Bool) : R[T;T⁻¹] :=
  if a then positivePart (q .incoming b)
  else -reciprocalField (nonpositivePart (q .preceding b))

/-- The next earlier node retains the positive part of the predecessor incoming error. -/
def arithmeticFourthEarlierField (b : Bool) : R[T;T⁻¹] := positivePart (q .preceding b)

/-- Both common terminal branches retain the positive closing fields. -/
def arithmeticFourthTerminalField (b : Bool) : R[T;T⁻¹] := positivePart (q .closing b)

local notation "V" => arithmeticFourthLastField hπ data H j hj u hu
local notation "P" => arithmeticFourthPrecedingField hπ data H j hj u hu

/-- The last retained node has no linear drift on either full puncture. -/
theorem arithmeticFourthLastField_linear (b a : Bool) : (V b a).coeff 1 = 0 := by
  cases a <;> simp only [arithmeticFourthLastField, Bool.false_eq_true, ↓reduceIte,
    AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, reciprocalField_coeff,
    nonpositivePart_coeff] <;> norm_num

/-- Both last-node fields vanish at the original boundary origin. -/
theorem arithmeticFourthLastField_boundary (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (V b a).coeff d = 0 := by
  cases a
  · change (-reciprocalField (nonpositivePart (q .incoming b))).coeff d = 0
    rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply,
      reciprocal_nonpositive_coeff _ d hd, neg_zero]
  · exact reciprocal_nonpositive_coeff _ d hd

/-- The predecessor incoming field has zero linear coefficient. -/
theorem arithmeticFourthPrecedingField_incoming_linear (b : Bool) :
    (P b false).coeff 1 = 0 := by
  simp only [arithmeticFourthPrecedingField, Bool.false_eq_true, ↓reduceIte,
    AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, reciprocalField_coeff,
    nonpositivePart_coeff]
  norm_num

/-- Both predecessor fields vanish at their full node boundary origins. -/
theorem arithmeticFourthPrecedingField_boundary (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (P b a).coeff d = 0 := by
  cases a
  · change (-reciprocalField (nonpositivePart (q .preceding b))).coeff d = 0
    rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply,
      reciprocal_nonpositive_coeff _ d hd, neg_zero]
  · change (positivePart (q .incoming b)).coeff d = 0
    rw [positivePart_coeff, ite_eq_right (by omega)]

/-- Scale both last-node fields once to the fourth arithmetic order. -/
def arithmeticFourthLastIntegralField (b a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 3 (V b a)

/-- Scale both predecessor fields while keeping their distinct smoothing contributions. -/
def arithmeticFourthPrecedingIntegralField (b a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 3 (P b a)

/-- The next earlier correction is also of order three over the same integral coefficients. -/
def arithmeticFourthEarlierIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 3 (arithmeticFourthEarlierField hπ data H j hj u hu b)

/-- The common terminal fields are lifted at the same fourth order. -/
def arithmeticFourthTerminalIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 3 (arithmeticFourthTerminalField hπ data H j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
