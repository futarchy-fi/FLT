/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedResidualTerminalLift
public import FLT.Mazur.PolygonArithmeticTwoBranchFirstIdentification

/-!
# Identification of the lifted terminal correction at first order

The entire composed lift, with its explicit common source identification,
is the original terminal factor built from both actual residual fields.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu
local notation "q" => arithmeticTerminalIntegralField hπ data H j hj u hu
local notation "s" => twoBranchCorrectionSmoothing R π 1 σ q

/-- Whole-node equality with the old first-order factor, including the source identification. -/
theorem arithmeticResidualTerminalLift_first :
    (arithmeticResidualTerminalLift hπ data H j hj u hu 1).toAlgHom.toRingHom =
      (arithmeticFirstResidualTerminalFactor hπ data H j hj u hu).toAlgHom.toRingHom.comp
        (ringMap (RingHom.id _) s σ
          (arithmeticResidualTerminalLift_smoothing_first hπ data H j hj u hu)) := by
  rw [arithmeticResidualTerminalLift_def]
  exact twoBranchCorrectionNodeFactor_first R π σ
    (arithmeticFirstChangedSmoothing_annihilated data H j hj u hu) q
    (arithmeticFirstResidualField hπ data H j hj u hu)
    (arithmeticTerminalIntegralField_first hπ data H j hj u hu)

end FLT.Mazur.WeierstrassDividedDepth
