/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdOuterIdentification
public import FLT.Mazur.PolygonSmoothingPunctureIdentification

/-!
# Third-layer identification of every full corrected node puncture

Each substitution is recovered from its whole-node factor. The predecessor
and terminal keep their actual old smoothings throughout the comparison.
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
local notation "Q" => Quotient R π 3
local notation "e" => parameter R π 3 ^ 3
local notation "he" => nextCorrectionParameter_square R π 2
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 3
local notation "s" => arithmeticSecondPrecedingSmoothing hπ data H 3 j hj u hu
local notation "t" => arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu 3
local notation "V" => arithmeticThirdLastIntegralField hπ data H j hj u hu
local notation "P" => arithmeticThirdPrecedingIntegralField hπ data H j hj u hu
local notation "T" => arithmeticThirdTerminalIntegralField hπ data H j hj u hu
local notation "E" => arithmeticThirdEarlierIntegralField hπ data H j hj u hu
local notation "p" => arithmeticThirdLastLayerField hπ data H j hj u hu
local notation "r" => arithmeticThirdPrecedingLayerField hπ data H j hj u hu
local notation "q" => arithmeticThirdResidualField hπ data H j hj u hu

/-- Both last-node punctures are the full prescribed third-layer substitutions. -/
theorem arithmeticThirdLastPuncture_third (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 3 τ (V b) a =
      LaurentSquareZeroAutomorphism.equiv e he (p b a) := by
  apply punctureFactor_source_identification _ τ
    (arithmeticThirdLastSmoothing_pair hπ data H j hj u hu 3 b)
    (arithmeticThirdLastFactor hπ data H j hj u hu 3 b)
    (arithmeticThirdLastLayerFactor hπ data H j hj u hu b) _ _ a
    (arithmeticThirdLastFactor_third hπ data H j hj u hu b)
    (arithmeticThirdLastFactor_puncture hπ data H j hj u hu 3 b a)
  have hh := squareZeroTwoBranchFactor_boundary τ e he
    (arithmeticTopSmoothing_annihilated data H 3) (p b) a
  rw [arithmeticThirdLastLayerField_positive] at hh
  cases a <;> exact hh

/-- Both predecessor punctures are identified on its exact second corrected smoothing. -/
theorem arithmeticThirdPrecedingPuncture_third (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 3 (s b) (P b) a =
      LaurentSquareZeroAutomorphism.equiv e he (r b a) := by
  apply punctureFactor_source_identification _ (s b)
    (arithmeticThirdPrecedingSmoothing_third hπ data H j hj u hu b)
    (arithmeticThirdPrecedingFactor hπ data H j hj u hu 3 b)
    (arithmeticThirdPrecedingLayerFactor hπ data H j hj u hu b) _ _ a
    (arithmeticThirdPrecedingFactor_third hπ data H j hj u hu b)
    (arithmeticThirdPrecedingFactor_puncture hπ data H j hj u hu 3 b a)
  have hh := squareZeroTwoBranchFactor_boundary (s b) e he
    (arithmeticThirdPrecedingInput_annihilated hπ data H j hj u hu b) (r b) a
  rw [arithmeticThirdPrecedingLayerField_positive] at hh
  cases a <;> exact hh

/-- Both rebased terminal punctures recover the complete positive closing fields. -/
theorem arithmeticThirdTerminalPuncture_third (b : Bool) :
    twoBranchCorrectionRebasedPunctureFactor R π 3 t T b =
      LaurentSquareZeroAutomorphism.equiv e he (positivePart (q .closing b)) := by
  apply punctureFactor_rebased_identification _ t
    (arithmeticThirdTerminalSmoothing_third hπ data H j hj u hu)
    (arithmeticThirdTerminalFactor hπ data H j hj u hu 3)
    (arithmeticThirdTerminalLayerFactor hπ data H j hj u hu) _ _ b
    (arithmeticThirdTerminalFactor_third hπ data H j hj u hu)
    (arithmeticThirdTerminalFactor_puncture hπ data H j hj u hu 3 b)
  have hh := squareZeroTwoBranchFactor_boundary t e he
    (arithmeticThirdTerminalInput_annihilated hπ data H j hj u hu) (q .closing) b
  cases b <;> exact hh

/-- The earlier outgoing substitution is the full positive predecessor residual field. -/
theorem arithmeticThirdEarlierPuncture_third (b : Bool) :
    correctionPunctureFactor R π 3 τ (E b) true =
      LaurentSquareZeroAutomorphism.equiv e he (positivePart (q .preceding b)) := by
  apply punctureFactor_source_identification _ τ
    (arithmeticThirdEarlierSmoothing_third hπ data H j hj u hu b)
    (arithmeticThirdEarlierFactor hπ data H j hj u hu 3 b)
    (arithmeticThirdEarlierLayerFactor hπ data H j hj u hu b) _ _ true
    (arithmeticThirdEarlierFactor_third hπ data H j hj u hu b)
    (arithmeticThirdEarlierFactor_puncture hπ data H j hj u hu 3 b true)
  exact squareZeroPositiveFactor_left τ e he
    (arithmeticTopSmoothing_annihilated data H 3) (q .preceding b)

/-- The earlier opposite puncture has no third-layer error. -/
theorem arithmeticThirdEarlierPuncture_opposite_third (b : Bool) :
    correctionPunctureFactor R π 3 τ (E b) false = AlgEquiv.refl := by
  apply punctureFactor_source_identification _ τ
    (arithmeticThirdEarlierSmoothing_third hπ data H j hj u hu b)
    (arithmeticThirdEarlierFactor hπ data H j hj u hu 3 b)
    (arithmeticThirdEarlierLayerFactor hπ data H j hj u hu b) _ _ false
    (arithmeticThirdEarlierFactor_third hπ data H j hj u hu b)
    (arithmeticThirdEarlierFactor_puncture hπ data H j hj u hu 3 b false)
  exact squareZeroPositiveFactor_right τ e he
    (arithmeticTopSmoothing_annihilated data H 3) (q .preceding b)

end FLT.Mazur.WeierstrassDividedDepth
