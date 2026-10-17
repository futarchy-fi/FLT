/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFirstFields
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification
public import FLT.Mazur.PolygonArithmeticIteratedSmoothingAnnihilator

/-!
# Full first node factors for the depth-zero initial edge

Both factors start at the original Mobius smoothing. The same last-node factor
has both punctures and retains its full incoming scalar drift at every order.
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
def arithmeticZeroFirstInitialIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 0 (arithmeticZeroFirstInitialField hπ data H j hj u hu b)

/-- Fix both full last-node inputs once over the original integral ring. -/
def arithmeticZeroFirstLastIntegralField (b a : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 0 (arithmeticZeroFirstLastField hπ data H j hj u hu b a)

variable (m : ℕ)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticZeroFirstInitialIntegralField hπ data H j hj u hu
local notation "V" => arithmeticZeroFirstLastIntegralField hπ data H j hj u hu

/-- The initial node keeps the full correction smoothing at arbitrary order. -/
def arithmeticZeroFirstInitialSmoothing (b : Bool) : Q :=
  correctionSmoothing R π m τ (A b)

/-- The full initial factor will transport the original initial open. -/
def arithmeticZeroFirstInitialFactor (b : Bool) :
    ChartRing (arithmeticZeroFirstInitialSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing τ := correctionNodeFactor R π m τ (A b)

/-- The last node retains both resulting scalar drifts. -/
def arithmeticZeroFirstLastSmoothing (b : Bool) : Q :=
  twoBranchCorrectionSmoothing R π m τ (V b)

/-- A single whole-node factor provides both initial and closing corrections. -/
def arithmeticZeroFirstLastFactor (b : Bool) :
    ChartRing (arithmeticZeroFirstLastSmoothing hπ data H j hj u hu m b) ≃ₐ[Q]
      ChartRing τ := twoBranchCorrectionNodeFactor R π m τ (V b)

/-- The exact last smoothing retains the measured initial linear error. -/
theorem arithmeticZeroFirstLastSmoothing_eq (b : Bool) :
    arithmeticZeroFirstLastSmoothing hπ data H j hj u hu m b =
      (1 - parameter R π m * algebraMap R Q
        ((arithmeticFourthZeroFirstIntegralField hπ data H j hj u hu b).coeff 1)) * τ := by
  unfold arithmeticZeroFirstLastSmoothing twoBranchCorrectionSmoothing
  rw [arithmeticZeroFirstLastIntegralField, correctionSmoothing_higher,
    arithmeticZeroFirstLastIntegralField, correctionSmoothing_higher]
  change (1 + parameter R π m ^ 1 * algebraMap R Q ((0 : R[T;T⁻¹]).coeff 1)) * _ = _
  rw [show (0 : R[T;T⁻¹]).coeff 1 = 0 from rfl, map_zero, mul_zero, add_zero, one_mul,
    arithmeticZeroFirstLastField_linear, map_neg, mul_neg, ← sub_eq_add_neg, pow_one]

/-- Both initial punctures come from the one full node factor. -/
theorem arithmeticZeroFirstInitialFactor_puncture (b a : Bool) :
    (punctureLaurentMap τ a).comp
        (arithmeticZeroFirstInitialFactor hπ data H j hj u hu m b).toAlgHom =
      (correctionPunctureFactor R π m τ (A b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticZeroFirstInitialSmoothing hπ data H j hj u hu m b) a) :=
  correctionNodeFactor_puncture R π m τ (A b) a

/-- The initial and closing punctures belong to the same full last factor. -/
theorem arithmeticZeroFirstLastFactor_puncture (b a : Bool) :
    (punctureLaurentMap τ a).comp
        (arithmeticZeroFirstLastFactor hπ data H j hj u hu m b).toAlgHom =
      (twoBranchCorrectionPunctureFactor R π m τ (V b) a).toAlgHom.comp
        (punctureLaurentMap (arithmeticZeroFirstLastSmoothing hπ data H j hj u hu m b) a) :=
  twoBranchCorrectionNodeFactor_puncture R π m τ (V b) a

end FLT.Mazur.WeierstrassDividedDepth
