/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondResidualPunctures
public import FLT.Mazur.PolygonSmoothingPunctureIdentification

/-!
# Full puncture identification for the actual second correction

The complete higher Laurent substitutions recover the constructed
square-zero factors at stage two, including the opposite retained puncture.
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
local notation "Q" => Quotient R π 2
local notation "e" => parameter R π 2 ^ 2
local notation "he" => nextCorrectionParameter_square R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 2
local notation "s" => arithmeticResidualLiftTerminalSmoothing hπ data H 2 j hj u hu
local notation "p" => arithmeticSecondResidualField hπ data H j hj u hu false
local notation "A" => arithmeticSecondResidualLiftRetainedPuncture hπ data H 2 j hj u hu
local notation "S" => arithmeticSecondResidualLiftTerminalPuncture hπ data H 2 j hj u hu

/-- Both complete terminal substitutions recover their positive square-zero fields. -/
theorem arithmeticSecondResidualLiftTerminalPuncture_second (b : Bool) :
    S b = LaurentSquareZeroAutomorphism.equiv e he (positivePart (p b)) := by
  apply punctureFactor_rebased_identification _ s
    (arithmeticSecondResidualLiftSmoothing_second hπ data H j hj u hu)
    (arithmeticSecondResidualLiftTerminalFactor hπ data H j hj u hu 2)
    (arithmeticSecondResidualTerminalFactor hπ data H j hj u hu) _ _ b
    (arithmeticSecondResidualLiftTerminalFactor_second hπ data H j hj u hu)
    (arithmeticSecondResidualLiftTerminalFactor_puncture hπ data H j hj u hu 2 b)
  have hh := squareZeroTwoBranchFactor_boundary s e he
    (arithmeticSecondResidualSmoothing_annihilated hπ data H j hj u hu) p b
  cases b <;> exact hh

/-- The complete outgoing retained substitution recovers its reciprocal complementary field. -/
theorem arithmeticSecondResidualLiftRetainedPuncture_second (b : Bool) :
    A b true = LaurentSquareZeroAutomorphism.equiv e he
      (reciprocalField (nonpositivePart (p b))) := by
  apply punctureFactor_source_identification _ τ
    (arithmeticSecondRetainedSmoothing hπ data H j hj u hu 2 b)
    (arithmeticSecondResidualLiftRetainedFactor hπ data H j hj u hu 2 b)
    (arithmeticSecondResidualRetainedFactor hπ data H j hj u hu b) _ _ true
    (arithmeticSecondResidualLiftRetainedFactor_second hπ data H j hj u hu b)
    (arithmeticSecondResidualLiftRetainedFactor_puncture hπ data H j hj u hu 2 b true)
  exact squareZeroReciprocalFactor_left τ e he
    (arithmeticSecondSmoothing_annihilated data H) (p b)

/-- This new correction fixes the opposite puncture on layer two; the old incoming error remains. -/
theorem arithmeticSecondResidualLiftRetainedPuncture_opposite_second (b : Bool) :
    A b false = AlgEquiv.refl := by
  apply punctureFactor_source_identification _ τ
    (arithmeticSecondRetainedSmoothing hπ data H j hj u hu 2 b)
    (arithmeticSecondResidualLiftRetainedFactor hπ data H j hj u hu 2 b)
    (arithmeticSecondResidualRetainedFactor hπ data H j hj u hu b) _ _ false
    (arithmeticSecondResidualLiftRetainedFactor_second hπ data H j hj u hu b)
    (arithmeticSecondResidualLiftRetainedFactor_puncture hπ data H j hj u hu 2 b false)
  exact arithmeticSecondResidualRetainedFactor_opposite hπ data H j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
