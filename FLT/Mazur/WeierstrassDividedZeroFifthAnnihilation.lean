/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFifthNodes
public import FLT.Mazur.WeierstrassDividedZeroFourthAnnihilation
public import FLT.Mazur.PolygonArithmeticIteratedSmoothingAnnihilator

/-!
# Annihilators on the actual fourth depth-zero smoothings

The fourth last-node drift and all accumulated terminal drifts survive.
Their top-power annihilators supply the fifth puncture identifications.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)

/-- The initial input retains its fourth correction drift at every arithmetic order. -/
theorem arithmeticZeroFifthInitialInput_annihilated (m : ℕ) (b : Bool) :
    parameter R π m ^ m * arithmeticZeroFourthInitialSmoothing hπ data H j hj u hu m b = 0 := by
  apply correctionSmoothing_annihilated
  exact arithmeticZeroFourthInitialInput_annihilated hπ data H j hj u hu m b

/-- Both fourth last-node drifts preserve the original top-power annihilator. -/
theorem arithmeticZeroFifthLastInput_annihilated (m : ℕ) (b : Bool) :
    parameter R π m ^ m * arithmeticZeroFourthLastSmoothing hπ data H j hj u hu m b = 0 := by
  apply twoBranchCorrectionSmoothing_annihilated
  exact arithmeticZeroFourthLastInput_annihilated hπ data H j hj u hu m b

/-- The entire common terminal input includes all accumulated inverse drifts. -/
theorem arithmeticZeroFifthTerminalInput_annihilated (m : ℕ) :
    parameter R π m ^ m * arithmeticZeroFourthTerminalSmoothing hπ data H j hj u hu m = 0 := by
  apply twoBranchCorrectionRebasedSmoothing_annihilated
  exact arithmeticZeroFourthTerminalInput_annihilated hπ data H j hj u hu m

end FLT.Mazur.WeierstrassDividedDepth
