/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondResidualFactors

/-!
# Actual higher arithmetic lifts of the second closing correction

Split the newly constructed integral second residual fields and scale them
by pi. The full existing node factors then give second corrections at every
order, retaining both punctures and the exact common terminal smoothing.
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
local notation "q" => arithmeticSecondResidualIntegralField hπ data H j hj u hu false

/-- The positive integral second field, scaled for the existing full arithmetic construction. -/
def arithmeticSecondTerminalIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 1 (positivePart (q b))

/-- The complementary integral second field in the retained reciprocal coordinate. -/
def arithmeticSecondRetainedIntegralField (b : Bool) : R[T;T⁻¹] :=
  higherCorrectionField R π 1 (reciprocalField (nonpositivePart (q b)))

local notation "P" => arithmeticSecondTerminalIntegralField hπ data H j hj u hu
local notation "N" => arithmeticSecondRetainedIntegralField hπ data H j hj u hu

/-- The retained correction has no smoothing drift because its linear coefficient vanishes. -/
theorem arithmeticSecondRetainedIntegralField_linear (b : Bool) : (N b).coeff 1 = 0 := by
  rw [arithmeticSecondRetainedIntegralField, higherCorrectionField_coeff,
    reciprocalField_coeff, nonpositivePart_coeff]
  norm_num

/-- The positive field vanishes at the original boundary origin over the integral ring. -/
theorem arithmeticSecondTerminalIntegralField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (P b).coeff d = 0 := by
  exact higherCorrectionField_boundary R π 1 _
    (fun k hk ↦ by rw [positivePart_coeff, ite_eq_right (by omega)]) d hd

/-- The reciprocal field also vanishes at its original boundary origin before specialization. -/
theorem arithmeticSecondRetainedIntegralField_boundary (b : Bool) (d : ℤ) (hd : d ≤ 0) :
    (N b).coeff d = 0 :=
  higherCorrectionField_boundary R π 1 _ (reciprocal_nonpositive_coeff (q b)) d hd

variable (m : ℕ)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticResidualLiftTerminalSmoothing hπ data H m j hj u hu

/-- The next terminal outgoing coordinate carries the entire positive field in order two. -/
theorem arithmeticSecondTerminalPuncture_coordinate (t : Q) (b : Bool) :
    correctionPunctureFactor R π m t (P b) true (T 1) =
      T 1 + C (parameter R π m ^ 2) * positivePart (correctionField R π m (q b)) := by
  rw [arithmeticSecondTerminalIntegralField,
    correctionPunctureFactor_higher_coordinate R π m 1 t _
      (fun k hk ↦ by rw [positivePart_coeff, ite_eq_right (by omega)]), correctionField_positive]

/-- The next retained coordinate carries the entire reciprocal complementary second field. -/
theorem arithmeticSecondRetainedPuncture_coordinate (t : Q) (b : Bool) :
    correctionPunctureFactor R π m t (N b) true (T 1) =
      T 1 + C (parameter R π m ^ 2) *
        reciprocalField (nonpositivePart (correctionField R π m (q b))) := by
  rw [arithmeticSecondRetainedIntegralField,
    correctionPunctureFactor_higher_coordinate R π m 1 t _
      (reciprocal_nonpositive_coeff (q b)), correctionField_reciprocal]

/-- The second retained correction preserves the original smoothing at every order. -/
theorem arithmeticSecondRetainedSmoothing (b : Bool) :
    correctionSmoothing R π m τ (N b) = τ := by
  rw [correctionSmoothing, arithmeticSecondRetainedIntegralField_linear, map_zero,
    mul_zero, add_zero, one_mul]

/-- The new common terminal smoothing retains the exact product of both second scalar drifts. -/
def arithmeticSecondResidualLiftSmoothing : Q :=
  twoBranchCorrectionRebasedSmoothing R π m s P

/-- The actual next terminal correction starts on the previously corrected full node. -/
def arithmeticSecondResidualLiftTerminalFactor :
    ChartRing s ≃ₐ[Q]
      ChartRing (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m) :=
  twoBranchCorrectionRebasedFactor R π m s P

/-- The actual next retained correction on its proved equal source smoothing. -/
def arithmeticSecondResidualLiftRetainedFactor (b : Bool) :
    ChartRing (correctionSmoothing R π m τ (N b)) ≃ₐ[Q] ChartRing τ :=
  correctionNodeFactor R π m τ (N b)

/-- Both terminal punctures retain their exact higher-order substitutions. -/
theorem arithmeticSecondResidualLiftTerminalFactor_puncture (b : Bool) :
    (punctureLaurentMap (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m) b).comp
        (arithmeticSecondResidualLiftTerminalFactor hπ data H j hj u hu m).toAlgHom =
      (twoBranchCorrectionRebasedPunctureFactor R π m s P b).toAlgHom.comp
        (punctureLaurentMap s b) :=
  twoBranchCorrectionRebasedFactor_puncture R π m s P b

/-- Both punctures of the next retained factor keep the entire opposite compensating inverse. -/
theorem arithmeticSecondResidualLiftRetainedFactor_puncture (b a : Bool) :
    (punctureLaurentMap τ a).comp
        (arithmeticSecondResidualLiftRetainedFactor hπ data H j hj u hu m b).toAlgHom =
      (correctionPunctureFactor R π m τ (N b) a).toAlgHom.comp
        (punctureLaurentMap (correctionSmoothing R π m τ (N b)) a) :=
  correctionNodeFactor_puncture R π m τ (N b) a

/-- The second correction starts from the actual first corrected quotient-compatible smoothing. -/
theorem arithmeticSecondResidualInputSmoothing_restriction :
    restriction R π m (arithmeticResidualLiftTerminalSmoothing hπ data H (m + 1) j hj u hu) =
      s :=
  twoBranchCorrectionRebasedSmoothing_restriction R π m _ _
    (arithmeticTerminalChangedSmoothing_restriction data H m j hj u hu hπ) _

/-- The next full common terminal smoothing preserves every original adjacent quotient. -/
theorem arithmeticSecondResidualLiftSmoothing_restriction :
    restriction R π m (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu (m + 1)) =
      arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m :=
  twoBranchCorrectionRebasedSmoothing_restriction R π m _ _
    (arithmeticSecondResidualInputSmoothing_restriction hπ data H j hj u hu m) P

/-- The next full terminal node factor has the original coefficient square on both coordinates. -/
theorem arithmeticSecondResidualLiftTerminalFactor_restriction :
    (ringMap (restriction R π m).toRingHom
        (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu (m + 1))
        (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m)
        (arithmeticSecondResidualLiftSmoothing_restriction hπ data H j hj u hu m)).comp
      (arithmeticSecondResidualLiftTerminalFactor hπ data H j hj u hu (m + 1)).toAlgHom.toRingHom =
    (arithmeticSecondResidualLiftTerminalFactor hπ data H j hj u hu m).toAlgHom.toRingHom.comp
      (ringMap (restriction R π m).toRingHom
        (arithmeticResidualLiftTerminalSmoothing hπ data H (m + 1) j hj u hu) s
        (arithmeticSecondResidualInputSmoothing_restriction hπ data H j hj u hu m)) :=
  twoBranchCorrectionRebasedFactor_restriction R π m _ _
    (arithmeticSecondResidualInputSmoothing_restriction hπ data H j hj u hu m) P

end FLT.Mazur.WeierstrassDividedDepth
