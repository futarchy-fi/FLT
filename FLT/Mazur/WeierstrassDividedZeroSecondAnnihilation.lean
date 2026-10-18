/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSecondNodes
public import FLT.Mazur.WeierstrassDividedFourthSmoothingAnnihilation
public import FLT.Mazur.PolygonArithmeticIteratedSmoothingAnnihilator

/-!
# Annihilators on the actual first depth-zero smoothings

The first last-node drift and all four old terminal drifts survive.
Their top-power annihilators supply the second puncture identifications.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- The initial input retains its first correction drift at every arithmetic order. -/
theorem arithmeticZeroSecondInitialInput_annihilated (m : ℕ) (b : Bool) :
    parameter R π m ^ m * arithmeticZeroFirstInitialSmoothing hπ data H j hj u hu m b = 0 := by
  apply correctionSmoothing_annihilated
  exact arithmeticTopSmoothing_annihilated data H m

/-- Both first last-node drifts preserve the original top-power annihilator. -/
theorem arithmeticZeroSecondLastInput_annihilated (m : ℕ) (b : Bool) :
    parameter R π m ^ m * arithmeticZeroFirstLastSmoothing hπ data H j hj u hu m b = 0 := by
  apply twoBranchCorrectionSmoothing_annihilated
  exact arithmeticTopSmoothing_annihilated data H m

/-- The entire common terminal input includes all four old inverse drifts. -/
theorem arithmeticZeroSecondTerminalInput_annihilated (m : ℕ) :
    parameter R π m ^ m * arithmeticFourthTerminalSmoothing hπ data H j hj u hu m = 0 := by
  apply twoBranchCorrectionRebasedSmoothing_annihilated
  exact arithmeticFourthTerminalInput_annihilated hπ data H j hj u hu m

end FLT.Mazur.WeierstrassDividedDepth
