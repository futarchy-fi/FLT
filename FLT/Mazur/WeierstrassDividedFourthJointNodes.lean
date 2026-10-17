/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthJointFields
public import FLT.Mazur.WeierstrassDividedThirdJointRestriction

/-!
# Full fourth-layer node corrections with the exact prior smoothings

The last node preserves its smoothing. The predecessor, earlier node and
terminal all start at their actual third-round smoothings. These factors
have not yet been installed into a fourth global atlas.
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
local notation "V" => arithmeticFourthLastIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFourthPrecedingIntegralField hπ data H j hj u hu
local notation "T" => arithmeticFourthTerminalIntegralField hπ data H j hj u hu
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "sE" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticThirdTerminalSmoothing hπ data H j hj u hu m

/-- Either last-node correction preserves any input smoothing at every arithmetic order. -/
theorem arithmeticFourthLastSmoothing (x : Q) (b a : Bool) :
    correctionSmoothing R π m x (V b a) = x := by
  rw [correctionSmoothing, arithmeticFourthLastIntegralField, higherCorrectionField_coeff,
    arithmeticFourthLastField_linear, mul_zero, map_zero, mul_zero, add_zero, one_mul]

/-- The shared full fourth correction preserves the last node's exact smoothing. -/
theorem arithmeticFourthLastSmoothing_pair (b : Bool) :
    twoBranchCorrectionSmoothing R π m τ (V b) = τ := by
  unfold twoBranchCorrectionSmoothing
  rw [arithmeticFourthLastSmoothing, arithmeticFourthLastSmoothing]

/-- Both fields live on one entire last retained node factor. -/
def arithmeticFourthLastFactor (b : Bool) :
    ChartRing (twoBranchCorrectionSmoothing R π m τ (V b)) ≃ₐ[Q] ChartRing τ :=
  twoBranchCorrectionNodeFactor R π m τ (V b)

/-- The predecessor starts from its actual third-round smoothing. -/
def arithmeticFourthPrecedingSmoothing (b : Bool) : Q :=
  twoBranchCorrectionSmoothing R π m (s b) (P b)

/-- Only its positive outgoing field contributes to the new exact scalar drift. -/
theorem arithmeticFourthPrecedingSmoothing_eq (b : Bool) :
    arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m b =
      (1 + parameter R π m ^ 4 * algebraMap R Q
        ((arithmeticFourthPrecedingField hπ data H j hj u hu b true).coeff 1)) * s b := by
  have hi : correctionSmoothing R π m (s b) (P b false) = s b := by
    rw [correctionSmoothing, arithmeticFourthPrecedingIntegralField, higherCorrectionField_coeff,
      arithmeticFourthPrecedingField_incoming_linear, mul_zero, map_zero, mul_zero,
      add_zero, one_mul]
  rw [arithmeticFourthPrecedingSmoothing, twoBranchCorrectionSmoothing, hi,
    arithmeticFourthPrecedingIntegralField, correctionSmoothing_higher]

/-- The predecessor's two full fields use its changed source, including all older drift. -/
def arithmeticFourthPrecedingFactor (b : Bool) :
    ChartRing (arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (s b) := twoBranchCorrectionNodeFactor R π m (s b) (P b)

/-- The next earlier node also keeps its exact new smoothing. -/
def arithmeticFourthEarlierSmoothing (b : Bool) : Q :=
  correctionSmoothing R π m (sE b) (arithmeticFourthEarlierIntegralField hπ data H j hj u hu b)

/-- The full earlier-node factor, to be installed only when an earlier retained label exists. -/
def arithmeticFourthEarlierFactor (b : Bool) :
    ChartRing (arithmeticFourthEarlierSmoothing hπ data H j hj u hu m b) ≃ₐ[Q] ChartRing (sE b) :=
  correctionNodeFactor R π m (sE b) (arithmeticFourthEarlierIntegralField hπ data H j hj u hu b)

/-- Both terminal corrections start at the actual third corrected terminal parameter. -/
def arithmeticFourthTerminalSmoothing : Q := twoBranchCorrectionRebasedSmoothing R π m t T

/-- The common full terminal factor retains the product of both new scalar drifts. -/
def arithmeticFourthTerminalFactor :
    ChartRing t ≃ₐ[Q] ChartRing (arithmeticFourthTerminalSmoothing hπ data H j hj u hu m) :=
  twoBranchCorrectionRebasedFactor R π m t T

/-- Both full last-node punctures come from the same whole-node correction. -/
theorem arithmeticFourthLastFactor_puncture (b a : Bool) :
    (punctureLaurentMap τ a).comp (arithmeticFourthLastFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m τ (V b) a).toAlgHom.comp
        (punctureLaurentMap (twoBranchCorrectionSmoothing R π m τ (V b)) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m τ (V b) a

/-- Both predecessor punctures retain its exact old and new parameters. -/
theorem arithmeticFourthPrecedingFactor_puncture (b a : Bool) :
    (punctureLaurentMap (s b) a).comp
        (arithmeticFourthPrecedingFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m b) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m (s b) (P b) a

/-- Both full earlier punctures retain the remaining opposite compensation. -/
theorem arithmeticFourthEarlierFactor_puncture (b a : Bool) :
    (punctureLaurentMap (sE b) a).comp
        (arithmeticFourthEarlierFactor hπ data H j hj u hu m b).toAlgHom =
      (correctionPunctureFactor R π m (sE b)
        (arithmeticFourthEarlierIntegralField hπ data H j hj u hu b) a).toAlgHom.comp
          (punctureLaurentMap (arithmeticFourthEarlierSmoothing hπ data H j hj u hu m b) a) :=
  correctionNodeFactor_puncture R π m (sE b) _ a

/-- Both terminal substitutions belong to the same full rebased terminal factor. -/
theorem arithmeticFourthTerminalFactor_puncture (b : Bool) :
    (punctureLaurentMap (arithmeticFourthTerminalSmoothing hπ data H j hj u hu m) b).comp
        (arithmeticFourthTerminalFactor hπ data H j hj u hu m).toAlgHom =
      (twoBranchCorrectionRebasedPunctureFactor R π m t T b).toAlgHom.comp
        (punctureLaurentMap t b) :=
  twoBranchCorrectionRebasedFactor_puncture R π m t T b

end FLT.Mazur.WeierstrassDividedDepth
