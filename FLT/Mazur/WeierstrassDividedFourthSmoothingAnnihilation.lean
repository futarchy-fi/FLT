/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthJointRestriction
public import FLT.Mazur.PolygonArithmeticIteratedSmoothingAnnihilator

/-!
# Higher-layer annihilators on the actual fourth correction inputs

The predecessor, earlier and terminal inputs keep all accumulated third-round
drifts. Their top-power annihilators hold at every arithmetic stage.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- The predecessor's full third smoothing retains the top-power annihilator at every stage. -/
theorem arithmeticFourthPrecedingInput_annihilated (m : ℕ) (b : Bool) :
    parameter R π m ^ m * arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m b = 0 := by
  apply twoBranchCorrectionSmoothing_annihilated
  apply correctionSmoothing_annihilated
  exact arithmeticTopSmoothing_annihilated data H m

/-- The earlier node's exact third smoothing also retains that annihilator at every stage. -/
theorem arithmeticFourthEarlierInput_annihilated (m : ℕ) (b : Bool) :
    parameter R π m ^ m * arithmeticThirdEarlierSmoothing hπ data H j hj u hu m b = 0 := by
  apply correctionSmoothing_annihilated
  exact arithmeticTopSmoothing_annihilated data H m

/-- All three inverse terminal drifts preserve the original top-power annihilator. -/
theorem arithmeticFourthTerminalInput_annihilated (m : ℕ) :
    parameter R π m ^ m * arithmeticThirdTerminalSmoothing hπ data H j hj u hu m = 0 := by
  apply twoBranchCorrectionRebasedSmoothing_annihilated
  apply twoBranchCorrectionRebasedSmoothing_annihilated
  apply twoBranchCorrectionRebasedSmoothing_annihilated
  unfold arithmeticTerminalChangedSmoothing
  rw [← mul_assoc, mul_comm (parameter R π m ^ m), mul_assoc,
    arithmeticTopSmoothing_annihilated data H m, mul_zero]

/-- At layer four, the predecessor correction fixes its full third input smoothing. -/
theorem arithmeticFourthPrecedingSmoothing_fourth (b : Bool) :
    arithmeticFourthPrecedingSmoothing hπ data H j hj u hu 4 b =
      arithmeticThirdPrecedingSmoothing hπ data H j hj u hu 4 b :=
  twoBranchCorrectionSmoothing_higher_eq R π 4 3 _
    (arithmeticFourthPrecedingInput_annihilated hπ data H j hj u hu 4 b) _

/-- The earlier correction fixes its exact previous smoothing on the fourth layer. -/
theorem arithmeticFourthEarlierSmoothing_fourth (b : Bool) :
    arithmeticFourthEarlierSmoothing hπ data H j hj u hu 4 b =
      arithmeticThirdEarlierSmoothing hπ data H j hj u hu 4 b :=
  correctionSmoothing_higher_eq R π 4 3 _
    (arithmeticFourthEarlierInput_annihilated hπ data H j hj u hu 4 b) _

/-- The terminal's fourth inverse drift fixes its entire third input smoothing at layer four. -/
theorem arithmeticFourthTerminalSmoothing_fourth :
    arithmeticFourthTerminalSmoothing hπ data H j hj u hu 4 =
      arithmeticThirdTerminalSmoothing hπ data H j hj u hu 4 :=
  twoBranchCorrectionRebasedSmoothing_higher_eq R π 4 3 _
    (arithmeticFourthTerminalInput_annihilated hπ data H j hj u hu 4) _

end FLT.Mazur.WeierstrassDividedDepth
