/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdJointNodes

/-!
# Third-layer annihilation on the actual old node smoothings

The top arithmetic power annihilates the normalized node at every stage.
At stage three this also annihilates the predecessor's second drift and the
terminal's two accumulated inverse drifts, without replacing those smoothings.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 3
local notation "e" => parameter R π 3 ^ 3
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 3
local notation "s" => arithmeticSecondPrecedingSmoothing hπ data H 3 j hj u hu
local notation "t" => arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu 3

omit hπ [IsDomain R] j hj u hu in
/-- The top arithmetic power annihilates the full original retained smoothing at every stage. -/
theorem arithmeticTopSmoothing_annihilated (m : ℕ) :
    parameter R π m ^ m * arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m = 0 := by
  rw [← arithmeticStartOneQuotient_relation]
  calc
    _ = parameter R π m ^ (m + 1) *
        (arithmeticStartOneQuotient W H.a1_unit π m : Quotient R π m) := by
      rw [pow_succ (parameter R π m) m, mul_assoc]
    _ = 0 := by rw [parameter_pow R π m, zero_mul]

/-- The predecessor's actual second smoothing has the required third-layer annihilator. -/
theorem arithmeticThirdPrecedingInput_annihilated (b : Bool) : e * s b = 0 := by
  unfold arithmeticSecondPrecedingSmoothing correctionSmoothing
  rw [mul_left_comm e, arithmeticTopSmoothing_annihilated data H 3, mul_zero]

omit hπ [IsDomain R] in
/-- The changed terminal smoothing already has the third-layer annihilator. -/
theorem arithmeticThirdChangedInput_annihilated :
    e * arithmeticTerminalChangedSmoothing data H 3 j hj u hu = 0 := by
  unfold arithmeticTerminalChangedSmoothing
  rw [← mul_assoc, mul_comm e, mul_assoc, arithmeticTopSmoothing_annihilated data H 3,
    mul_zero]

/-- The first inverse rebase preserves the third-layer annihilator of the full terminal node. -/
theorem arithmeticThirdResidualInput_annihilated :
    e * arithmeticResidualLiftTerminalSmoothing hπ data H 3 j hj u hu = 0 := by
  unfold arithmeticResidualLiftTerminalSmoothing twoBranchCorrectionRebasedSmoothing
  rw [mul_left_comm e, arithmeticThirdChangedInput_annihilated data H j hj u hu, mul_zero]

/-- Both accumulated inverse drifts preserve annihilation on the actual third input terminal. -/
theorem arithmeticThirdTerminalInput_annihilated : e * t = 0 := by
  unfold arithmeticSecondResidualLiftSmoothing twoBranchCorrectionRebasedSmoothing
  rw [mul_left_comm e, arithmeticThirdResidualInput_annihilated hπ data H j hj u hu, mul_zero]

/-- At stage three both new predecessor drifts vanish on its exact previous smoothing. -/
theorem arithmeticThirdPrecedingSmoothing_third (b : Bool) :
    arithmeticThirdPrecedingSmoothing hπ data H j hj u hu 3 b = s b :=
  twoBranchCorrectionSmoothing_higher_eq R π 3 2 (s b)
    (arithmeticThirdPrecedingInput_annihilated hπ data H j hj u hu b) _

/-- The earlier retained node's third correction preserves its original smoothing at stage three. -/
theorem arithmeticThirdEarlierSmoothing_third (b : Bool) :
    arithmeticThirdEarlierSmoothing hπ data H j hj u hu 3 b = τ :=
  correctionSmoothing_higher_eq R π 3 2 τ (arithmeticTopSmoothing_annihilated data H 3) _

/-- The new inverse terminal drift vanishes on its actual old smoothing at stage three. -/
theorem arithmeticThirdTerminalSmoothing_third :
    arithmeticThirdTerminalSmoothing hπ data H j hj u hu 3 = t :=
  twoBranchCorrectionRebasedSmoothing_higher_eq R π 3 2 t
    (arithmeticThirdTerminalInput_annihilated hπ data H j hj u hu) _

end FLT.Mazur.WeierstrassDividedDepth
