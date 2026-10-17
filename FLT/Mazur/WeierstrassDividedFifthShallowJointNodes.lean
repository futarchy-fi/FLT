/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowJointFields
public import FLT.Mazur.WeierstrassDividedFourthJointRestriction

/-!
# Full fifth-layer node corrections with the exact prior smoothings

The last node preserves its smoothing. The predecessor and terminal start
at their actual fourth-round smoothings. These factors
have not yet been installed into a fifth global atlas.
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
local notation "V" => arithmeticFifthShallowLastIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFifthShallowPrecedingIntegralField hπ data H j hj u hu
local notation "T" => arithmeticFifthShallowTerminalIntegralField hπ data H j hj u hu
local notation "s" => arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticFourthTerminalSmoothing hπ data H j hj u hu m

/-- Either last-node correction preserves any input smoothing at every arithmetic order. -/
theorem arithmeticFifthShallowLastSmoothing (x : Q) (b a : Bool) :
    correctionSmoothing R π m x (V b a) = x := by
  rw [correctionSmoothing, arithmeticFifthShallowLastIntegralField, higherCorrectionField_coeff,
    arithmeticFifthShallowLastField_linear, mul_zero, map_zero, mul_zero, add_zero, one_mul]

/-- The shared full fifth correction preserves the last node's exact smoothing. -/
theorem arithmeticFifthShallowLastSmoothing_pair (b : Bool) :
    twoBranchCorrectionSmoothing R π m τ (V b) = τ := by
  unfold twoBranchCorrectionSmoothing
  rw [arithmeticFifthShallowLastSmoothing, arithmeticFifthShallowLastSmoothing]

/-- Both fields live on one entire last retained node factor. -/
def arithmeticFifthShallowLastFactor (b : Bool) :
    ChartRing (twoBranchCorrectionSmoothing R π m τ (V b)) ≃ₐ[Q] ChartRing τ :=
  twoBranchCorrectionNodeFactor R π m τ (V b)

/-- The predecessor starts from its actual fourth-round smoothing. -/
def arithmeticFifthShallowPrecedingSmoothing (b : Bool) : Q :=
  twoBranchCorrectionSmoothing R π m (s b) (P b)

/-- Only its positive outgoing field contributes to the new exact scalar drift. -/
theorem arithmeticFifthShallowPrecedingSmoothing_eq (b : Bool) :
    arithmeticFifthShallowPrecedingSmoothing hπ data H j hj u hu m b =
      (1 + parameter R π m ^ 5 * algebraMap R Q
        ((arithmeticFifthShallowPrecedingField hπ data H j hj u hu b true).coeff 1)) * s b := by
  have hi : correctionSmoothing R π m (s b) (P b false) = s b := by
    rw [correctionSmoothing, arithmeticFifthShallowPrecedingIntegralField,
      higherCorrectionField_coeff,
      arithmeticFifthShallowPrecedingField_incoming_linear, mul_zero, map_zero, mul_zero,
      add_zero, one_mul]
  rw [arithmeticFifthShallowPrecedingSmoothing, twoBranchCorrectionSmoothing, hi,
    arithmeticFifthShallowPrecedingIntegralField, correctionSmoothing_higher]

/-- The predecessor's two full fields use its changed source, including all older drift. -/
def arithmeticFifthShallowPrecedingFactor (b : Bool) :
    ChartRing (arithmeticFifthShallowPrecedingSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (s b) := twoBranchCorrectionNodeFactor R π m (s b) (P b)

/-- Both terminal corrections start at the actual fourth corrected terminal parameter. -/
def arithmeticFifthShallowTerminalSmoothing : Q := twoBranchCorrectionRebasedSmoothing R π m t T

/-- The common full terminal factor retains the product of both new scalar drifts. -/
def arithmeticFifthShallowTerminalFactor :
    ChartRing t ≃ₐ[Q] ChartRing (arithmeticFifthShallowTerminalSmoothing hπ data H j hj u hu m) :=
  twoBranchCorrectionRebasedFactor R π m t T

/-- Both full last-node punctures come from the same whole-node correction. -/
theorem arithmeticFifthShallowLastFactor_puncture (b a : Bool) :
    (punctureLaurentMap τ a).comp
        (arithmeticFifthShallowLastFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m τ (V b) a).toAlgHom.comp
        (punctureLaurentMap (twoBranchCorrectionSmoothing R π m τ (V b)) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m τ (V b) a

/-- Both predecessor punctures retain its exact old and new parameters. -/
theorem arithmeticFifthShallowPrecedingFactor_puncture (b a : Bool) :
    (punctureLaurentMap (s b) a).comp
        (arithmeticFifthShallowPrecedingFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticFifthShallowPrecedingSmoothing hπ data H j hj u hu m b) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m (s b) (P b) a

/-- Both terminal substitutions belong to the same full rebased terminal factor. -/
theorem arithmeticFifthShallowTerminalFactor_puncture (b : Bool) :
    (punctureLaurentMap (arithmeticFifthShallowTerminalSmoothing hπ data H j hj u hu m) b).comp
        (arithmeticFifthShallowTerminalFactor hπ data H j hj u hu m).toAlgHom =
      (twoBranchCorrectionRebasedPunctureFactor R π m t T b).toAlgHom.comp
        (punctureLaurentMap t b) :=
  twoBranchCorrectionRebasedFactor_puncture R π m t T b

end FLT.Mazur.WeierstrassDividedDepth
