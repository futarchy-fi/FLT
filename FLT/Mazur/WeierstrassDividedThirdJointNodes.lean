/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdJointFields

/-!
# Full third-layer node corrections with the exact prior smoothings

The last node preserves its smoothing. The predecessor starts at its actual
second-round smoothing and retains the new drift. The terminal also starts
at its previously corrected smoothing. These are full node factors, before
installation in a third global atlas.
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
  (m : ℕ)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "V" => arithmeticThirdLastIntegralField hπ data H j hj u hu
local notation "P" => arithmeticThirdPrecedingIntegralField hπ data H j hj u hu
local notation "T" => arithmeticThirdTerminalIntegralField hπ data H j hj u hu
local notation "s" => arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu
local notation "t" => arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m

/-- Either last-node correction preserves any input smoothing at every arithmetic order. -/
theorem arithmeticThirdLastSmoothing (x : Q) (b a : Bool) :
    correctionSmoothing R π m x (V b a) = x := by
  rw [correctionSmoothing, arithmeticThirdLastIntegralField, higherCorrectionField_coeff,
    arithmeticThirdLastField_linear, mul_zero, map_zero, mul_zero, add_zero, one_mul]

/-- The shared full third correction preserves the last node's exact smoothing. -/
theorem arithmeticThirdLastSmoothing_pair (b : Bool) :
    twoBranchCorrectionSmoothing R π m τ (V b) = τ := by
  unfold twoBranchCorrectionSmoothing
  rw [arithmeticThirdLastSmoothing, arithmeticThirdLastSmoothing]

/-- Both fields live on one entire last retained node factor. -/
def arithmeticThirdLastFactor (b : Bool) :
    ChartRing (twoBranchCorrectionSmoothing R π m τ (V b)) ≃ₐ[Q] ChartRing τ :=
  twoBranchCorrectionNodeFactor R π m τ (V b)

/-- The predecessor starts from its actual second-round smoothing. -/
def arithmeticThirdPrecedingSmoothing (b : Bool) : Q :=
  twoBranchCorrectionSmoothing R π m (s b) (P b)

/-- Only its positive outgoing field contributes to the new exact scalar drift. -/
theorem arithmeticThirdPrecedingSmoothing_eq (b : Bool) :
    arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m b =
      (1 + parameter R π m ^ 3 * algebraMap R Q
        ((arithmeticThirdPrecedingField hπ data H j hj u hu b true).coeff 1)) * s b := by
  have hi : correctionSmoothing R π m (s b) (P b false) = s b := by
    rw [correctionSmoothing, arithmeticThirdPrecedingIntegralField, higherCorrectionField_coeff,
      arithmeticThirdPrecedingField_incoming_linear, mul_zero, map_zero, mul_zero,
      add_zero, one_mul]
  rw [arithmeticThirdPrecedingSmoothing, twoBranchCorrectionSmoothing, hi,
    arithmeticThirdPrecedingIntegralField, correctionSmoothing_higher]

/-- The predecessor's two full fields use its changed source, including all older drift. -/
def arithmeticThirdPrecedingFactor (b : Bool) :
    ChartRing (arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (s b) := twoBranchCorrectionNodeFactor R π m (s b) (P b)

/-- The next earlier node also keeps its exact new smoothing. -/
def arithmeticThirdEarlierSmoothing (b : Bool) : Q :=
  correctionSmoothing R π m τ (arithmeticThirdEarlierIntegralField hπ data H j hj u hu b)

/-- The full earlier-node factor, to be installed only when an earlier retained label exists. -/
def arithmeticThirdEarlierFactor (b : Bool) :
    ChartRing (arithmeticThirdEarlierSmoothing hπ data H j hj u hu m b) ≃ₐ[Q] ChartRing τ :=
  correctionNodeFactor R π m τ (arithmeticThirdEarlierIntegralField hπ data H j hj u hu b)

/-- Both terminal corrections start at the actual second corrected terminal parameter. -/
def arithmeticThirdTerminalSmoothing : Q := twoBranchCorrectionRebasedSmoothing R π m t T

/-- The common full terminal factor retains the product of both new scalar drifts. -/
def arithmeticThirdTerminalFactor :
    ChartRing t ≃ₐ[Q] ChartRing (arithmeticThirdTerminalSmoothing hπ data H j hj u hu m) :=
  twoBranchCorrectionRebasedFactor R π m t T

/-- Both full last-node punctures come from the same whole-node correction. -/
theorem arithmeticThirdLastFactor_puncture (b a : Bool) :
    (punctureLaurentMap τ a).comp (arithmeticThirdLastFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m τ (V b) a).toAlgHom.comp
        (punctureLaurentMap (twoBranchCorrectionSmoothing R π m τ (V b)) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m τ (V b) a

/-- Both predecessor punctures retain its exact old and new parameters. -/
theorem arithmeticThirdPrecedingFactor_puncture (b a : Bool) :
    (punctureLaurentMap (s b) a).comp
        (arithmeticThirdPrecedingFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m b) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m (s b) (P b) a

/-- Both full earlier punctures retain the remaining opposite compensation. -/
theorem arithmeticThirdEarlierFactor_puncture (b a : Bool) :
    (punctureLaurentMap τ a).comp
        (arithmeticThirdEarlierFactor hπ data H j hj u hu m b).toAlgHom =
      (correctionPunctureFactor R π m τ
        (arithmeticThirdEarlierIntegralField hπ data H j hj u hu b) a).toAlgHom.comp
          (punctureLaurentMap (arithmeticThirdEarlierSmoothing hπ data H j hj u hu m b) a) :=
  correctionNodeFactor_puncture R π m τ _ a

/-- Both terminal substitutions belong to the same full rebased terminal factor. -/
theorem arithmeticThirdTerminalFactor_puncture (b : Bool) :
    (punctureLaurentMap (arithmeticThirdTerminalSmoothing hπ data H j hj u hu m) b).comp
        (arithmeticThirdTerminalFactor hπ data H j hj u hu m).toAlgHom =
      (twoBranchCorrectionRebasedPunctureFactor R π m t T b).toAlgHom.comp
        (punctureLaurentMap t b) :=
  twoBranchCorrectionRebasedFactor_puncture R π m t T b

end FLT.Mazur.WeierstrassDividedDepth
