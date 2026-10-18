/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousState
public import FLT.Mazur.LaurentReciprocalRelativeCorrection
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# Simultaneous boundary fields at an arbitrary correction layer

The last node receives the incoming initial correction and the outgoing closing
correction together. Its incoming linear drift is retained at every layer.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticSimultaneous
open PolygonArithmeticStages LaurentPolynomial LaurentBoundaryVectorField
open LaurentBoundaryCorrectionSplit
variable {R : Type*} [CommRing R] (q : Bool → Bool → R[T;T⁻¹])

/-- The full initial relative error contributes its reciprocal nonpositive part. -/
def initialField (b : Bool) : R[T;T⁻¹] := reciprocalField (nonpositivePart (q false b))

/-- A single last node receives both the incoming and outgoing fields. -/
def lastField (b a : Bool) : R[T;T⁻¹] :=
  if a then reciprocalField (nonpositivePart (q true b)) else -positivePart (q false b)

/-- Both positive closing fields act on one common terminal. -/
def terminalField (b : Bool) : R[T;T⁻¹] := positivePart (q true b)

/-- The initial field extends across the origin. -/
theorem initialField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (initialField q b).coeff d = 0 := reciprocal_nonpositive_coeff _ d hd

/-- Both fields on the shared last node extend across their respective origins. -/
theorem lastField_boundary (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (lastField q b a).coeff d = 0 := by
  cases a
  · exact LaurentReciprocalRelativeCorrection.neighborField_boundary _ d hd
  · exact reciprocal_nonpositive_coeff _ d hd

/-- Both common terminal fields extend across their origins. -/
theorem terminalField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (terminalField q b).coeff d = 0 := by
  rw [terminalField, positivePart_coeff, ite_eq_right (by omega)]

/-- The last incoming linear coefficient is retained without any vanishing assumption. -/
theorem lastField_linear (b : Bool) : (lastField q b false).coeff 1 = -(q false b).coeff 1 := by
  change (-positivePart (q false b)).coeff 1 = _
  simp only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, positivePart_coeff,
    show (0 : ℤ) < 1 by omega, ↓reduceIte]

/-- The outgoing reciprocal nonpositive field has zero linear coefficient. -/
theorem lastField_outgoing_linear (b : Bool) : (lastField q b true).coeff 1 = 0 := by
  change (reciprocalField (nonpositivePart _)).coeff 1 = 0
  rw [reciprocalField_coeff, nonpositivePart_coeff]
  norm_num

variable (π : R) (m : ℕ)
local notation "e" => fun c b ↦ correctionField R π m (q c b)

/-- The initial split commutes with every coefficient specialization. -/
theorem initialField_spec (b : Bool) :
    correctionField R π m (initialField q b) = reciprocalField (nonpositivePart (e false b)) :=
  correctionField_reciprocal R π m _

/-- The incoming split commutes with every coefficient specialization. -/
theorem lastField_incoming_spec (b : Bool) :
    correctionField R π m (lastField q b false) = -positivePart (e false b) := by
  change correctionField R π m (-positivePart (q false b)) = _
  rw [show ∀ z : R[T;T⁻¹], correctionField R π m (-z) = -correctionField R π m z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap (algebraMap R (Quotient R π m))) z,
    correctionField_positive]

/-- The outgoing split commutes with every coefficient specialization. -/
theorem lastField_outgoing_spec (b : Bool) :
    correctionField R π m (lastField q b true) = reciprocalField (nonpositivePart (e true b)) :=
  correctionField_reciprocal R π m _

/-- The common terminal split commutes with every coefficient specialization. -/
theorem terminalField_spec (b : Bool) :
    correctionField R π m (terminalField q b) = positivePart (e true b) :=
  correctionField_positive R π m _

end FLT.Mazur.PolygonArithmeticSimultaneous
