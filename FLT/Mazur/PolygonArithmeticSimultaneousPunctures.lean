/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousStep

/-!
# Simultaneous full punctures at an arbitrary next layer

Both punctures of the shared last factor use the same actual input smoothing.
The common terminal keeps all accumulated inverse drifts.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticSimultaneous
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {π : R}
  (S : State R π) (r : ℕ) (q : Bool → Bool → R[T;T⁻¹])
local notation "Q" => Quotient R π (r + 1)
local notation "e" => parameter R π (r + 1) ^ (r + 1)
local notation "he" => nextCorrectionParameter_square R π r
local notation "A" => initialInput (π := π) r q
local notation "V" => lastInput (π := π) r q
local notation "T" => terminalInput (π := π) r q
local notation "F" => fun c b ↦ correctionField R π (r + 1) (q c b)

/-- The full initial puncture is the reciprocal nonpositive substitution at the next layer. -/
theorem State.initialPuncture_next (b : Bool) :
    correctionPunctureFactor R π (r + 1) (S.initial (r + 1) b) (A b) true =
      LaurentSquareZeroAutomorphism.equiv e he (reciprocalField (nonpositivePart (F false b))) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π (r + 1) _ (A b) true (LaurentPolynomial.T 1) = _
  rw [initialInput, correctionPunctureFactor_higher_coordinate]
  · rw [initialField_spec]
    exact (LaurentSquareZeroAutomorphism.equiv_T _ _ _).symm
  · exact initialField_boundary q b

/-- Both complete punctures of the same last node realize their specified fields. -/
theorem State.lastPuncture_next (hS : S.Annihilated) (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π (r + 1) (S.last (r + 1) b) (V b) a =
      LaurentSquareZeroAutomorphism.equiv e he
        (correctionField R π (r + 1) (lastField q b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π (r + 1) r he _
    (hS.2.1 (r + 1) b) _ (lastField_boundary q b) a

/-- Both full common terminal punctures realize the complete positive closing fields. -/
theorem State.terminalPuncture_next (hS : S.Annihilated) (b : Bool) :
    twoBranchCorrectionRebasedPunctureFactor R π (r + 1) (S.terminal (r + 1)) T b =
      LaurentSquareZeroAutomorphism.equiv e he (positivePart (F true b)) := by
  have h := twoBranchCorrectionRebasedPunctureFactor_higher_eq R π (r + 1) r he _
    (hS.2.2 (r + 1)) (terminalField q) (terminalField_boundary q) b
  rw [terminalField_spec] at h
  exact h

end FLT.Mazur.PolygonArithmeticSimultaneous
