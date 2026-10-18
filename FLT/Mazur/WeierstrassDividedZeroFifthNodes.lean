/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFifthSplit
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification
public import FLT.Mazur.PolygonArithmeticIteratedSmoothingAnnihilator

/-!
# Full fifth node factors on the actual fourth depth-zero smoothings

The initial and last factors start at their fourth corrected smoothings.
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
def arithmeticZeroFifthInitialIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 4 (arithmeticZeroFifthInitialField hπ data H j hj u hu b)

/-- Fix both full last-node inputs once over the original integral ring. -/
def arithmeticZeroFifthLastIntegralField (b a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 4 (arithmeticZeroFifthLastField hπ data H j hj u hu b a)

/-- The common terminal inputs are fixed once over the original integral ring. -/
def arithmeticZeroFifthTerminalIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 4 (arithmeticZeroFifthTerminalField hπ data H j hj u hu b)

variable (m : ℕ)
local notation "Q" => Quotient R π m
local notation "a" => arithmeticZeroFourthInitialSmoothing hπ data H j hj u hu m
local notation "s" => arithmeticZeroFourthLastSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticZeroFourthTerminalSmoothing hπ data H j hj u hu m
local notation "A" => arithmeticZeroFifthInitialIntegralField hπ data H j hj u hu
local notation "V" => arithmeticZeroFifthLastIntegralField hπ data H j hj u hu
local notation "T" => arithmeticZeroFifthTerminalIntegralField hπ data H j hj u hu

/-- The initial node keeps the full correction smoothing at arbitrary order. -/
def arithmeticZeroFifthInitialSmoothing (b : Bool) : Q :=
  correctionSmoothing R π m (a b) (A b)

/-- The full initial factor will transport the original initial open. -/
def arithmeticZeroFifthInitialFactor (b : Bool) :
    ChartRing (arithmeticZeroFifthInitialSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (a b) := correctionNodeFactor R π m (a b) (A b)

/-- The last node retains both resulting scalar drifts. -/
def arithmeticZeroFifthLastSmoothing (b : Bool) : Q :=
  twoBranchCorrectionSmoothing R π m (s b) (V b)

/-- A single whole-node factor provides both initial and closing corrections. -/
def arithmeticZeroFifthLastFactor (b : Bool) :
    ChartRing (arithmeticZeroFifthLastSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing (s b) := twoBranchCorrectionNodeFactor R π m (s b) (V b)

/-- The exact fifth last smoothing retains the new measured incoming linear drift. -/
theorem arithmeticZeroFifthLastSmoothing_eq (b : Bool) :
    arithmeticZeroFifthLastSmoothing hπ data H j hj u hu m b =
      (1 - parameter R π m ^ 5 * algebraMap R Q
        ((arithmeticZeroFifthIntegralField hπ data H j hj u hu false b).coeff 1)) * s b := by
  have hz : (arithmeticZeroFifthLastField hπ data H j hj u hu b true).coeff 1 = 0 := by
    change (LaurentBoundaryVectorField.reciprocalField
      (LaurentBoundaryCorrectionSplit.nonpositivePart _)).coeff 1 = 0
    rw [LaurentBoundaryVectorField.reciprocalField_coeff,
      LaurentBoundaryCorrectionSplit.nonpositivePart_coeff]
    norm_num
  unfold arithmeticZeroFifthLastSmoothing twoBranchCorrectionSmoothing
  rw [arithmeticZeroFifthLastIntegralField, correctionSmoothing_higher,
    arithmeticZeroFifthLastIntegralField, correctionSmoothing_higher,
    hz, map_zero, mul_zero, add_zero, one_mul, arithmeticZeroFifthLastField_linear,
    map_neg, mul_neg, ← sub_eq_add_neg]

/-- The common terminal retains its inverse product of both new drifts. -/
def arithmeticZeroFifthTerminalSmoothing : Q :=
  twoBranchCorrectionRebasedSmoothing R π m t T

/-- Both terminal branches belong to the same full rebased node factor. -/
def arithmeticZeroFifthTerminalFactor :
    ChartRing t ≃ₐ[Q] ChartRing (arithmeticZeroFifthTerminalSmoothing hπ data H j hj u hu m) :=
  twoBranchCorrectionRebasedFactor R π m t T

/-- Both initial punctures come from the one full node factor. -/
theorem arithmeticZeroFifthInitialFactor_puncture (b c : Bool) :
    (punctureLaurentMap (a b) c).comp
        (arithmeticZeroFifthInitialFactor hπ data H j hj u hu m b).toAlgHom =
      (correctionPunctureFactor R π m (a b) (A b) c).toAlgHom.comp
        (punctureLaurentMap (arithmeticZeroFifthInitialSmoothing hπ data H j hj u hu m b) c) :=
  correctionNodeFactor_puncture R π m (a b) (A b) c

/-- The initial and closing punctures belong to the same full last factor. -/
theorem arithmeticZeroFifthLastFactor_puncture (b c : Bool) :
    (punctureLaurentMap (s b) c).comp
        (arithmeticZeroFifthLastFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m (s b) (V b) c).toAlgHom.comp
        (punctureLaurentMap (arithmeticZeroFifthLastSmoothing hπ data H j hj u hu m b) c) :=
  twoBranchCorrectionNodeFactor_puncture R π m (s b) (V b) c

/-- Both terminal substitutions are induced by the single full terminal factor. -/
theorem arithmeticZeroFifthTerminalFactor_puncture (b : Bool) :
    (punctureLaurentMap (arithmeticZeroFifthTerminalSmoothing hπ data H j hj u hu m) b).comp
        (arithmeticZeroFifthTerminalFactor hπ data H j hj u hu m).toAlgHom =
      (twoBranchCorrectionRebasedPunctureFactor R π m t T b).toAlgHom.comp
        (punctureLaurentMap t b) :=
  twoBranchCorrectionRebasedFactor_puncture R π m t T b

end FLT.Mazur.WeierstrassDividedDepth
