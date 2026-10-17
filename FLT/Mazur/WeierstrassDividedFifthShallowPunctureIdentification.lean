/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowJointNodes
public import FLT.Mazur.WeierstrassDividedFifthShallowNodes
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# Complete fifth-layer punctures on the actual prior smoothings

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
local notation "e" => parameter R π 5 ^ 5
local notation "he" => nextCorrectionParameter_square R π 4
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 5
local notation "s" => arithmeticFourthPrecedingSmoothing hπ data H j hj u hu 5
local notation "t" => arithmeticFourthTerminalSmoothing hπ data H j hj u hu 5
local notation "V" => arithmeticFifthShallowLastIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFifthShallowPrecedingIntegralField hπ data H j hj u hu
local notation "T" => arithmeticFifthShallowTerminalIntegralField hπ data H j hj u hu
local notation "q" => arithmeticFifthResidualField hπ data H j hj u hu

/-- Both shared-node punctures realize the full fifth-order fields. -/
theorem arithmeticFifthShallowLastPuncture_fifth (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 5 τ (V b) a =
      LaurentSquareZeroAutomorphism.equiv e he
        (correctionField R π 5 (arithmeticFifthShallowLastField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 5 4 he τ
    (arithmeticTopSmoothing_annihilated data H 5) _
    (arithmeticFifthShallowLastField_boundary hπ data H j hj u hu b) a

/-- Both predecessor punctures retain its actual fourth smoothing in the identification. -/
theorem arithmeticFifthShallowPrecedingPuncture_fifth (b a : Bool) :
    twoBranchCorrectionPunctureFactor R π 5 (s b) (P b) a =
      LaurentSquareZeroAutomorphism.equiv e he
        (correctionField R π 5 (arithmeticFifthShallowPrecedingField hπ data H j hj u hu b a)) :=
  twoBranchCorrectionPunctureFactor_higher_eq R π 5 4 he (s b)
    (by
      apply twoBranchCorrectionSmoothing_annihilated
      exact arithmeticFourthPrecedingInput_annihilated hπ data H j hj u hu 5 b) _
    (arithmeticFifthShallowPrecedingField_boundary hπ data H j hj u hu b) a

/-- Both terminal punctures retain their complete positive closing fields. -/
theorem arithmeticFifthShallowTerminalPuncture_fifth (b : Bool) :
    twoBranchCorrectionRebasedPunctureFactor R π 5 t T b =
      LaurentSquareZeroAutomorphism.equiv e he (positivePart (q .closing b)) := by
  have h := twoBranchCorrectionRebasedPunctureFactor_higher_eq R π 5 4 he t
    (by
      apply twoBranchCorrectionRebasedSmoothing_annihilated
      exact arithmeticFourthTerminalInput_annihilated hπ data H j hj u hu 5)
    (arithmeticFifthShallowTerminalField hπ data H j hj u hu)
    (fun a d hd ↦ by
      change (positivePart _).coeff d = 0
      rw [positivePart_coeff, ite_eq_right (by omega)]) b
  change _ = LaurentSquareZeroAutomorphism.equiv e he
    (correctionField R π 5 (positivePart _)) at h
  rw [correctionField_positive, arithmeticFifthResidualIntegralField_spec] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
