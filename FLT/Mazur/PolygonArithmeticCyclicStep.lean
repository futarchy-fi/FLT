/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticCyclicState
public import FLT.Mazur.PolygonArithmeticSimultaneousSplit
public import FLT.Mazur.PolygonArithmeticIteratedSmoothingAnnihilator

/-!
# Correct both incident edges on every whole node of a cycle

The successor permutation also supplies each node's predecessor. Each node
receives one incoming and one outgoing field, including across the closing edge.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticCyclic
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {ι : Type*}
  (σ : Equiv.Perm ι) (q : ι → R[T;T⁻¹])

/-- The incoming positive error and outgoing complementary error share one whole node. -/
def nodeField (i : ι) (a : Bool) : R[T;T⁻¹] :=
  if a then reciprocalField (nonpositivePart (q i)) else -positivePart (q (σ.symm i))

/-- Both fields extend over their respective node origins. -/
theorem nodeField_boundary (i : ι) (a : Bool) (d : ℤ) (hd : d ≤ 0) :
    (nodeField σ q i a).coeff d = 0 := by
  cases a
  · exact LaurentReciprocalRelativeCorrection.neighborField_boundary _ d hd
  · exact reciprocal_nonpositive_coeff _ d hd

/-- The outgoing field has no linear drift. -/
theorem nodeField_outgoing_linear (i : ι) : (nodeField σ q i true).coeff 1 = 0 := by
  change (reciprocalField (nonpositivePart _)).coeff 1 = 0
  rw [reciprocalField_coeff, nonpositivePart_coeff]
  norm_num

/-- The incoming linear drift is kept with its actual sign and predecessor. -/
theorem nodeField_incoming_linear (i : ι) :
    (nodeField σ q i false).coeff 1 = -(q (σ.symm i)).coeff 1 := by
  change (-positivePart _).coeff 1 = _
  simp only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, positivePart_coeff,
    show (0 : ℤ) < 1 by omega, ↓reduceIte]

/-- Scale both incident fields at a single correction index. -/
def nodeInput (r : ℕ) (i : ι) (a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π r (nodeField σ q i a)

variable (S : State R π ι) (r : ℕ)
local notation "V" => nodeInput (π := π) σ q r

/-- Both punctures arise from the same complete node factor. -/
def State.punctureFactor (m : ℕ) (i : ι) (a : Bool) :
    (Quotient R π m)[T;T⁻¹] ≃ₐ[Quotient R π m] (Quotient R π m)[T;T⁻¹] :=
  twoBranchCorrectionPunctureFactor R π m (S.parameter m i) (V i) a

local notation "P" => S.punctureFactor σ q r

/-- Transport every full edge through its two incident whole-node factors. -/
def State.step : State R π ι where
  parameter m i := twoBranchCorrectionSmoothing R π m (S.parameter m i) (V i)
  edge m i := ((P m (σ i) false).trans (S.edge m i)).trans (P m i true).symm

/-- The full correction retains the exact old and new smoothing rings. -/
def State.nodeFactor (m : ℕ) (i : ι) :
    ChartRing ((S.step σ q r).parameter m i) ≃ₐ[Quotient R π m]
      ChartRing (S.parameter m i) :=
  twoBranchCorrectionNodeFactor R π m (S.parameter m i) (V i)

/-- Both full boundary squares are supplied by one whole-node isomorphism. -/
theorem State.nodeFactor_puncture (m : ℕ) (i : ι) (a : Bool) :
    (punctureLaurentMap (S.parameter m i) a).comp (S.nodeFactor σ q r m i).toAlgHom =
      (P m i a).toAlgHom.comp (punctureLaurentMap ((S.step σ q r).parameter m i) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m (S.parameter m i) (V i) a

/-- The exact smoothing drift includes the incoming edge's linear coefficient. -/
theorem State.step_parameter (m : ℕ) (i : ι) :
    (S.step σ q r).parameter m i =
      (1 - PolygonArithmeticStages.parameter R π m ^ (r + 1) *
        algebraMap R (Quotient R π m) ((q (σ.symm i)).coeff 1)) * S.parameter m i := by
  change twoBranchCorrectionSmoothing R π m (S.parameter m i) (V i) = _
  unfold twoBranchCorrectionSmoothing
  rw [nodeInput, correctionSmoothing_higher, nodeInput, correctionSmoothing_higher,
    nodeField_outgoing_linear, map_zero, mul_zero, add_zero, one_mul,
    nodeField_incoming_linear, map_neg, mul_neg, ← sub_eq_add_neg]

/-- Every smoothing keeps its top-power annihilator through the full cyclic step. -/
theorem State.step_annihilated (hS : S.Annihilated) : (S.step σ q r).Annihilated :=
  fun m i ↦ twoBranchCorrectionSmoothing_annihilated R π m _ _ (hS m i) _

/-- Both complete punctures realize their selected fields on the next layer. -/
theorem State.punctureFactor_next (hS : S.Annihilated) (i : ι) (a : Bool) :
    P (r + 1) i a =
      LaurentSquareZeroAutomorphism.equiv
        (PolygonArithmeticStages.parameter R π (r + 1) ^ (r + 1))
        (nextCorrectionParameter_square R π r)
        (correctionField R π (r + 1) (nodeField σ q i a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π (r + 1) r
    (nextCorrectionParameter_square R π r) _ (hS (r + 1) i) _ (nodeField_boundary σ q i) a

end FLT.Mazur.PolygonArithmeticCyclic
