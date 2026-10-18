/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSecondSplit
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification
public import FLT.Mazur.PolygonArithmeticIteratedSmoothingAnnihilator

/-!
# Full second node factors on the actual first depth-zero smoothings

The initial and last factors start at their first corrected smoothings.
The shared last node and common terminal retain every new scalar drift.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- Fix the full initial correction input in the uniform arithmetic convention. -/
def arithmeticZeroSecondInitialIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 1 (arithmeticZeroSecondInitialField hπ data H j hj u hu b)

/-- Fix both full last-node inputs once over the original integral ring. -/
def arithmeticZeroSecondLastIntegralField (b a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 1 (arithmeticZeroSecondLastField hπ data H j hj u hu b a)

/-- The common terminal inputs are fixed once over the original integral ring. -/
def arithmeticZeroSecondTerminalIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 1 (arithmeticZeroSecondTerminalField hπ data H j hj u hu b)

variable (m : ℕ)
local notation "Q" => Quotient R π m
local notation "a" => arithmeticZeroFirstInitialSmoothing hπ data H j hj u hu m
local notation "s" => arithmeticZeroFirstLastSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticFourthTerminalSmoothing hπ data H j hj u hu m
local notation "A" => arithmeticZeroSecondInitialIntegralField hπ data H j hj u hu
local notation "V" => arithmeticZeroSecondLastIntegralField hπ data H j hj u hu
local notation "T" => arithmeticZeroSecondTerminalIntegralField hπ data H j hj u hu

/-- The initial node keeps the full correction smoothing at arbitrary order. -/
def arithmeticZeroSecondInitialSmoothing (b : Bool) : Q :=
  correctionSmoothing R π m (a b) (A b)

/-- The full initial factor will transport the original initial open. -/
def arithmeticZeroSecondInitialFactor (b : Bool) :
    ChartRing (arithmeticZeroSecondInitialSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (a b) := correctionNodeFactor R π m (a b) (A b)

/-- The last node retains both resulting scalar drifts. -/
def arithmeticZeroSecondLastSmoothing (b : Bool) : Q :=
  twoBranchCorrectionSmoothing R π m (s b) (V b)

/-- A single whole-node factor provides both initial and closing corrections. -/
def arithmeticZeroSecondLastFactor (b : Bool) :
    ChartRing (arithmeticZeroSecondLastSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (s b) := twoBranchCorrectionNodeFactor R π m (s b) (V b)

/-- The exact second last smoothing retains the new measured incoming linear drift. -/
theorem arithmeticZeroSecondLastSmoothing_eq (b : Bool) :
    arithmeticZeroSecondLastSmoothing hπ data H j hj u hu m b =
      (1 - parameter R π m ^ 2 * algebraMap R Q
        ((arithmeticZeroSecondIntegralField hπ data H j hj u hu false b).coeff 1)) * s b := by
  have hz : (arithmeticZeroSecondLastField hπ data H j hj u hu b true).coeff 1 = 0 := by
    change (LaurentBoundaryVectorField.reciprocalField
      (LaurentBoundaryCorrectionSplit.nonpositivePart _)).coeff 1 = 0
    rw [LaurentBoundaryVectorField.reciprocalField_coeff,
      LaurentBoundaryCorrectionSplit.nonpositivePart_coeff]
    norm_num
  unfold arithmeticZeroSecondLastSmoothing twoBranchCorrectionSmoothing
  rw [arithmeticZeroSecondLastIntegralField, correctionSmoothing_higher,
    arithmeticZeroSecondLastIntegralField, correctionSmoothing_higher,
    hz, map_zero, mul_zero, add_zero, one_mul, arithmeticZeroSecondLastField_linear,
    map_neg, mul_neg, ← sub_eq_add_neg]

/-- The common terminal retains its inverse product of both new drifts. -/
def arithmeticZeroSecondTerminalSmoothing : Q :=
  twoBranchCorrectionRebasedSmoothing R π m t T

/-- Both terminal branches belong to the same full rebased node factor. -/
def arithmeticZeroSecondTerminalFactor :
    ChartRing t ≃ₐ[Q] ChartRing (arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu m) :=
  twoBranchCorrectionRebasedFactor R π m t T

/-- Both initial punctures come from the one full node factor. -/
theorem arithmeticZeroSecondInitialFactor_puncture (b c : Bool) :
    (punctureLaurentMap (a b) c).comp
        (arithmeticZeroSecondInitialFactor hπ data H j hj u hu m b).toAlgHom =
      (correctionPunctureFactor R π m (a b) (A b) c).toAlgHom.comp
        (punctureLaurentMap (arithmeticZeroSecondInitialSmoothing hπ data H j hj u hu m b) c) :=
  correctionNodeFactor_puncture R π m (a b) (A b) c

/-- The initial and closing punctures belong to the same full last factor. -/
theorem arithmeticZeroSecondLastFactor_puncture (b c : Bool) :
    (punctureLaurentMap (s b) c).comp
        (arithmeticZeroSecondLastFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m (s b) (V b) c).toAlgHom.comp
        (punctureLaurentMap (arithmeticZeroSecondLastSmoothing hπ data H j hj u hu m b) c) :=
  twoBranchCorrectionNodeFactor_puncture R π m (s b) (V b) c

/-- Both terminal substitutions are induced by the single full terminal factor. -/
theorem arithmeticZeroSecondTerminalFactor_puncture (b : Bool) :
    (punctureLaurentMap (arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu m) b).comp
        (arithmeticZeroSecondTerminalFactor hπ data H j hj u hu m).toAlgHom =
      (twoBranchCorrectionRebasedPunctureFactor R π m t T b).toAlgHom.comp
        (punctureLaurentMap t b) :=
  twoBranchCorrectionRebasedFactor_puncture R π m t T b

end FLT.Mazur.WeierstrassDividedDepth
