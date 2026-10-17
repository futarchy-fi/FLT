/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthSmoothingAnnihilation
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# Complete fourth-layer punctures on the actual prior smoothings

The shared and predecessor factors simultaneously realize their two full
fields. The earlier and terminal factors retain their accumulated drifts.
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
local notation "e" => parameter R π 4 ^ 4
local notation "he" => nextCorrectionParameter_square R π 3
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 4
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu 4
local notation "t" => arithmeticThirdTerminalSmoothing hπ data H j hj u hu 4
local notation "V" => arithmeticFourthLastIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFourthPrecedingIntegralField hπ data H j hj u hu
local notation "T" => arithmeticFourthTerminalIntegralField hπ data H j hj u hu
local notation "A" => arithmeticFourthEarlierIntegralField hπ data H j hj u hu
local notation "q" => arithmeticFourthResidualField hπ data H j hj u hu

/-- Both shared-node punctures realize the full fourth-order fields. -/
theorem arithmeticFourthLastPuncture_fourth (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 4 τ (V b) a =
      LaurentSquareZeroAutomorphism.equiv e he
        (correctionField R π 4 (arithmeticFourthLastField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 4 3 he τ
    (arithmeticTopSmoothing_annihilated data H 4) _
    (arithmeticFourthLastField_boundary hπ data H j hj u hu b) a

/-- Both predecessor punctures retain its actual third smoothing in the identification. -/
theorem arithmeticFourthPrecedingPuncture_fourth (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 4 (s b) (P b) a =
      LaurentSquareZeroAutomorphism.equiv e he
        (correctionField R π 4 (arithmeticFourthPrecedingField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 4 3 he (s b)
    (arithmeticFourthPrecedingInput_annihilated hπ data H j hj u hu 4 b) _
    (arithmeticFourthPrecedingField_boundary hπ data H j hj u hu b) a

/-- Both terminal punctures retain their complete positive closing fields. -/
theorem arithmeticFourthTerminalPuncture_fourth (b : Bool) :
    twoBranchCorrectionRebasedPunctureFactor R π 4 t T b =
      LaurentSquareZeroAutomorphism.equiv e he (positivePart (q .closing b)) := by
  have h := twoBranchCorrectionRebasedPunctureFactor_higher_eq R π 4 3 he t
    (arithmeticFourthTerminalInput_annihilated hπ data H j hj u hu 4)
    (arithmeticFourthTerminalField hπ data H j hj u hu)
    (fun a d hd ↦ by
      change (positivePart _).coeff d = 0
      rw [positivePart_coeff, ite_eq_right (by omega)]) b
  change _ = LaurentSquareZeroAutomorphism.equiv e he
    (correctionField R π 4 (positivePart _)) at h
  rw [correctionField_positive, arithmeticFourthResidualIntegralField_spec] at h
  exact h

/-- The earlier outgoing puncture is identified on its complete third smoothing. -/
theorem arithmeticFourthEarlierPuncture_fourth (b : Bool) :
    correctionPunctureFactor R π 4
        (arithmeticThirdEarlierSmoothing hπ data H j hj u hu 4 b) (A b) true =
      LaurentSquareZeroAutomorphism.equiv e he (positivePart (q .preceding b)) := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  change correctionPunctureFactor R π 4 _ (A b) true (LaurentPolynomial.T 1) = _
  rw [arithmeticFourthEarlierIntegralField, correctionPunctureFactor_higher_coordinate]
  · rw [arithmeticFourthEarlierField, correctionField_positive,
      arithmeticFourthResidualIntegralField_spec]
    exact (LaurentSquareZeroAutomorphism.equiv_T e he _).symm
  · intro d hd
    change (positivePart _).coeff d = 0
    rw [positivePart_coeff, ite_eq_right (by omega)]

end FLT.Mazur.WeierstrassDividedDepth
