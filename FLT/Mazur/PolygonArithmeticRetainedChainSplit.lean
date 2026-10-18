/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainPositions
public import FLT.Mazur.PolygonArithmeticSimultaneousSplit

/-!
# Split every retained-chain error between its actual adjacent nodes

Each retained node receives its incoming positive correction and outgoing
reciprocal nonpositive correction together, including both boundary nodes.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages LaurentPolynomial LaurentBoundaryVectorField
open LaurentBoundaryCorrectionSplit
variable {R : Type*} [CommRing R] {n : ℕ} (q : Edge n → Bool → R[T;T⁻¹])

/-- The initial node receives the nonpositive part of the original initial error. -/
def initialField (b : Bool) : R[T;T⁻¹] := reciprocalField (nonpositivePart (q .initial b))

/-- Both fields belong to the same retained node, with its actual incident edges. -/
def retainedField (i : Fin (n + 1)) (b a : Bool) : R[T;T⁻¹] :=
  if a then reciprocalField (nonpositivePart (q (outgoingEdge i) b))
  else -positivePart (q (incomingEdge i) b)

/-- The two closing positive parts correct one common terminal. -/
def terminalField (b : Bool) : R[T;T⁻¹] := positivePart (q .closing b)

/-- The initial field extends across its node origin. -/
theorem initialField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (initialField q b).coeff d = 0 := reciprocal_nonpositive_coeff _ d hd

/-- Both fields on every retained node extend across their respective origins. -/
theorem retainedField_boundary (i : Fin (n + 1)) (b a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (retainedField q i b a).coeff d = 0 := by
  cases a
  · exact LaurentReciprocalRelativeCorrection.neighborField_boundary _ d hd
  · exact reciprocal_nonpositive_coeff _ d hd

/-- Both common terminal fields extend across the origin. -/
theorem terminalField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (terminalField q b).coeff d = 0 := by
  rw [terminalField, positivePart_coeff, ite_eq_right (by omega)]

/-- Every incoming linear coefficient is retained, including the initial edge. -/
theorem retainedField_linear (i : Fin (n + 1)) (b : Bool) :
    (retainedField q i b false).coeff 1 = -(q (incomingEdge i) b).coeff 1 := by
  change (-positivePart _).coeff 1 = _
  simp only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, positivePart_coeff,
    show (0 : ℤ) < 1 by omega, ↓reduceIte]

/-- No outgoing reciprocal nonpositive correction has a linear coefficient. -/
theorem retainedField_outgoing_linear (i : Fin (n + 1)) (b : Bool) :
    (retainedField q i b true).coeff 1 = 0 := by
  change (reciprocalField (nonpositivePart _)).coeff 1 = 0
  rw [reciprocalField_coeff, nonpositivePart_coeff]
  norm_num

variable (π : R) (m : ℕ)
local notation "e" => fun c b ↦ correctionField R π m (q c b)

/-- The entire initial split commutes with coefficient specialization. -/
theorem initialField_spec (b : Bool) :
    correctionField R π m (initialField q b) =
      reciprocalField (nonpositivePart (e .initial b)) := correctionField_reciprocal R π m _

/-- Each incoming split commutes with coefficient specialization. -/
theorem retainedField_incoming_spec (i : Fin (n + 1)) (b : Bool) :
    correctionField R π m (retainedField q i b false) =
      -positivePart (e (incomingEdge i) b) := by
  change correctionField R π m (-positivePart _) = _
  rw [show ∀ z : R[T;T⁻¹], correctionField R π m (-z) = -correctionField R π m z from
    fun z ↦ map_neg (PolygonScalingNaturality.coeffMap (algebraMap R (Quotient R π m))) z,
    correctionField_positive]

/-- Each outgoing split commutes with coefficient specialization. -/
theorem retainedField_outgoing_spec (i : Fin (n + 1)) (b : Bool) :
    correctionField R π m (retainedField q i b true) =
      reciprocalField (nonpositivePart (e (outgoingEdge i) b)) :=
  correctionField_reciprocal R π m _

/-- Both terminal splits commute with coefficient specialization. -/
theorem terminalField_spec (b : Bool) :
    correctionField R π m (terminalField q b) = positivePart (e .closing b) :=
  correctionField_positive R π m _

end FLT.Mazur.PolygonArithmeticRetainedChain
