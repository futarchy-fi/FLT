/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainStep

/-!
# Full retained-chain punctures at the next correction layer

Both punctures of the shared retained factor use the same actual input smoothing.
The common terminal keeps all accumulated inverse drifts.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticRetainedChain
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R} {n : ℕ}
  (S : State R π n) (r : ℕ) (q : Edge n → Bool → R[T;T⁻¹])
local notation "Q" => Quotient R π (r + 1)
local notation "e" => parameter R π (r + 1) ^ (r + 1)
local notation "he" => nextCorrectionParameter_square R π r
local notation "A" => initialInput (π := π) r q
local notation "V" => retainedInput (π := π) r q
local notation "T" => terminalInput (π := π) r q
local notation "F" => fun c b ↦ correctionField R π (r + 1) (q c b)

/-- The full initial puncture realizes the next reciprocal nonpositive substitution. -/
theorem State.initialPuncture_next (b : Bool) :
    correctionPunctureFactor R π (r + 1) (S.initial (r + 1) b) (A b) true =
      LaurentSquareZeroAutomorphism.equiv e he
        (reciprocalField (nonpositivePart (F .initial b))) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π (r + 1) _ (A b) true (LaurentPolynomial.T 1) = _
  rw [initialInput, correctionPunctureFactor_higher_coordinate]
  · rw [initialField_spec]
    exact (LaurentSquareZeroAutomorphism.equiv_T _ _ _).symm
  · exact initialField_boundary q b

/-- Both complete punctures of the same retained node realize their two incident fields. -/
theorem State.retainedPuncture_next (hS : S.Annihilated) (i : Fin (n + 1)) (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π (r + 1) (S.retained (r + 1) i b) (V i b) a =
      LaurentSquareZeroAutomorphism.equiv e he
        (correctionField R π (r + 1) (retainedField q i b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π (r + 1) r he _
    (hS.2.1 (r + 1) i b) _ (retainedField_boundary q i b) a

/-- Every outgoing puncture realizes the entire nonpositive field in its edge coordinate. -/
theorem State.outgoingFactor_next (hS : S.Annihilated) (i : Fin (n + 1)) (b : Bool) :
    S.outgoingFactor r q (r + 1) i b =
      LaurentSquareZeroAutomorphism.equiv e he (nonpositivePart (F (outgoingEdge i) b)) := by
  rw [State.outgoingFactor, S.retainedPuncture_next r q hS,
    retainedField_outgoing_spec]
  apply AlgEquiv.coe_toAlgHom_injective
  change invert.toAlgHom.comp
    ((LaurentSquareZeroAutomorphism.subst e he
      (reciprocalField (nonpositivePart _))).comp invert.toAlgHom) = _
  rw [LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_involutive]
  rfl

/-- Both full common terminal punctures realize the complete positive closing fields. -/
theorem State.terminalPuncture_next (hS : S.Annihilated) (b : Bool) :
    twoBranchCorrectionRebasedPunctureFactor R π (r + 1) (S.terminal (r + 1)) T b =
      LaurentSquareZeroAutomorphism.equiv e he (positivePart (F .closing b)) := by
  have h := twoBranchCorrectionRebasedPunctureFactor_higher_eq R π (r + 1) r he _
    (hS.2.2 (r + 1)) (terminalField q) (terminalField_boundary q) b
  rw [terminalField_spec] at h
  exact h

end FLT.Mazur.PolygonArithmeticRetainedChain
