/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalFirstResidualFactors
public import FLT.Mazur.PolygonSmoothingSquareZeroFactorIndependence

/-!
# Independence from the chosen first-order residual quotient

Any finite Laurent fields realizing the two actual residual coordinates give
the same whole retained and terminal corrections. The chosen quotients need
not be equal: equality after weighting by the parameter is sufficient.
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
local notation "Q" => Quotient R π 1
local notation "L" => Q[T;T⁻¹]
local notation "e" => parameter R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu
local notation "D" => arithmeticTerminalResidualEquiv data H 1 j hj u hu
local notation "q" => arithmeticFirstResidualField hπ data H j hj u hu

/-- The weighted chosen quotient is uniquely determined by the original full coordinate. -/
theorem arithmeticFirstResidualField_weighted_unique (b : Bool) (p : L)
    (hp : D b (T 1) = T 1 + C e * p) : C e * q b = C e * p := by
  exact add_left_cancel
    ((arithmeticFirstResidualField_coordinate hπ data H j hj u hu b).symm.trans hp)

/-- Any quotient of the same residual gives exactly the same full retained automorphism. -/
theorem arithmeticFirstResidualRetainedFactor_choice (b : Bool) (p : L)
    (hp : D b (T 1) = T 1 + C e * p) :
    arithmeticFirstResidualRetainedFactor hπ data H j hj u hu b =
      squareZeroReciprocalFactor τ e (parameter_pow R π 1)
        (by rw [mul_comm]; exact arithmeticFirstSmoothing_mul_parameter data H) p :=
  squareZeroReciprocalFactor_congr _ _ _ _
    (arithmeticFirstResidualField_weighted_unique hπ data H j hj u hu b p hp)

/-- Both division choices disappear simultaneously from the complete terminal automorphism. -/
theorem arithmeticFirstResidualTerminalFactor_choice (p : Bool → L)
    (hp : ∀ b, D b (T 1) = T 1 + C e * p b) :
    arithmeticFirstResidualTerminalFactor hπ data H j hj u hu =
      squareZeroTwoBranchFactor σ e (parameter_pow R π 1)
        (arithmeticFirstChangedSmoothing_annihilated data H j hj u hu) p :=
  squareZeroTwoBranchFactor_congr _ _ _ _
    (fun b ↦ arithmeticFirstResidualField_weighted_unique hπ data H j hj u hu b (p b) (hp b))

/-- The whole overlap reparametrization is independent of the chosen residual quotient too. -/
theorem arithmeticFirstResidualOverlapFactor_choice (b : Bool) (p : L)
    (hp : D b (T 1) = T 1 + C e * p) :
    arithmeticFirstResidualOverlapFactor hπ data H j hj u hu b =
      invert.trans ((LaurentSquareZeroAutomorphism.equiv e (parameter_pow R π 1)
        (LaurentBoundaryVectorField.reciprocalField
          (LaurentBoundaryCorrectionSplit.nonpositivePart p))).trans invert) := by
  unfold arithmeticFirstResidualOverlapFactor
  rw [squareZeroReciprocalEquiv_congr e (parameter_pow R π 1)
    (arithmeticFirstResidualField_weighted_unique hπ data H j hj u hu b p hp)]

end FLT.Mazur.WeierstrassDividedDepth
