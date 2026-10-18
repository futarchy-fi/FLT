/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroThirdNodes
public import FLT.Mazur.WeierstrassDividedZeroSecondAnnihilation
public import FLT.Mazur.PolygonArithmeticIteratedSmoothingAnnihilator

/-!
# Annihilators on the actual second depth-zero smoothings

The second last-node drift and all accumulated terminal drifts survive.
Their top-power annihilators supply the third puncture identifications.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- The initial input retains its second correction drift at every arithmetic order. -/
theorem arithmeticZeroThirdInitialInput_annihilated (m : ℕ) (b : Bool) :
    parameter R π m ^ m * arithmeticZeroSecondInitialSmoothing hπ data H j hj u hu m b = 0 := by
  apply correctionSmoothing_annihilated
  exact arithmeticZeroSecondInitialInput_annihilated hπ data H j hj u hu m b

/-- Both second last-node drifts preserve the original top-power annihilator. -/
theorem arithmeticZeroThirdLastInput_annihilated (m : ℕ) (b : Bool) :
    parameter R π m ^ m * arithmeticZeroSecondLastSmoothing hπ data H j hj u hu m b = 0 := by
  apply twoBranchCorrectionSmoothing_annihilated
  exact arithmeticZeroSecondLastInput_annihilated hπ data H j hj u hu m b

/-- The entire common terminal input includes all accumulated inverse drifts. -/
theorem arithmeticZeroThirdTerminalInput_annihilated (m : ℕ) :
    parameter R π m ^ m * arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu m = 0 := by
  apply twoBranchCorrectionRebasedSmoothing_annihilated
  exact arithmeticZeroSecondTerminalInput_annihilated hπ data H j hj u hu m

end FLT.Mazur.WeierstrassDividedDepth
