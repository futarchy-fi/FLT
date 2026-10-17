/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalResidualFiltration
public import FLT.Mazur.WeierstrassDividedTerminalFirstOrderConstraint
public import FLT.Mazur.PolygonSmoothingSquareZeroTwoBranches

/-!
# Whole-node factors of the actual first-order residual closing transitions

The vector fields are obtained from the original arithmetic substitutions.
Both terminal factors act on one node, and each retained factor fixes its
opposite puncture. Every Laurent coefficient is kept in the factorization.
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
local notation "Q" => Quotient R π 1
local notation "L" => Q[T;T⁻¹]
local notation "e" => parameter R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu
local notation "a" => arithmeticTerminalTangentScale data H 1 j hj u hu
local notation "D" => arithmeticTerminalResidualEquiv data H 1 j hj u hu

/-- A finite vector field obtained from the entire original residual Laurent coordinate. -/
def arithmeticFirstResidualField (b : Bool) : L :=
  (arithmeticTerminalResidual_coordinate hπ data H 0 j hj u hu b).choose

local notation "q" => arithmeticFirstResidualField hπ data H j hj u hu

/-- The field retains the full original coordinate, rather than a selected tangent. -/
theorem arithmeticFirstResidualField_coordinate (b : Bool) :
    D b (T 1) = T 1 + C e * q b :=
  (arithmeticTerminalResidual_coordinate hπ data H 0 j hj u hu b).choose_spec

/-- The full original residual algebra map is the specified square-zero substitution. -/
theorem arithmeticFirstResidual_subst (b : Bool) :
    (D b).toAlgHom = LaurentSquareZeroAutomorphism.subst e (parameter_pow R π 1) (q b) :=
  LaurentSquareZeroAutomorphism.eq_subst _ _ _ _
    (arithmeticFirstResidualField_coordinate hπ data H j hj u hu b)

omit hπ [IsDomain R] in
/-- The corrected terminal smoothing is also annihilated by the first-order parameter. -/
theorem arithmeticFirstChangedSmoothing_annihilated : e * σ = 0 := by
  unfold arithmeticTerminalChangedSmoothing
  calc
    _ = (a true : Q) * a false * (τ * e) := by ring
    _ = 0 := by rw [arithmeticFirstSmoothing_mul_parameter data H, mul_zero]

/-- The single full terminal node correction, with both prescribed positive fields. -/
def arithmeticFirstResidualTerminalFactor : ChartRing σ ≃ₐ[Q] ChartRing σ :=
  squareZeroTwoBranchFactor σ e (parameter_pow R π 1)
    (arithmeticFirstChangedSmoothing_annihilated data H j hj u hu) q

/-- Each retained node carries the full complementary correction in its own coordinate. -/
def arithmeticFirstResidualRetainedFactor (b : Bool) : ChartRing τ ≃ₐ[Q] ChartRing τ :=
  squareZeroReciprocalFactor τ e (parameter_pow R π 1)
    (by rw [mul_comm]; exact arithmeticFirstSmoothing_mul_parameter data H) (q b)

/-- The complementary full Laurent transition in the original closing orientation. -/
def arithmeticFirstResidualOverlapFactor (b : Bool) : L ≃ₐ[Q] L :=
  invert.trans ((LaurentSquareZeroAutomorphism.equiv e (parameter_pow R π 1)
    (reciprocalField (nonpositivePart (q b)))).trans invert)

local notation "F" => arithmeticFirstResidualTerminalFactor hπ data H j hj u hu
local notation "K" => arithmeticFirstResidualOverlapFactor hπ data H j hj u hu

/-- Both actual residual boundaries factor through the same full terminal node correction. -/
theorem arithmeticFirstResidual_boundary (b : Bool) :
    (D b).toAlgHom.comp
        (if b then leftLaurentMap σ else (leftLaurentMap σ).comp (branchSwapMap σ)) =
      (K b).toAlgHom.comp
        ((if b then leftLaurentMap σ else (leftLaurentMap σ).comp (branchSwapMap σ)).comp
          (F).toAlgHom) := by
  rw [arithmeticFirstResidual_subst hπ data H j hj u hu]
  change _ = (K b).toAlgHom.comp
    ((if b then leftLaurentMap σ else (leftLaurentMap σ).comp (branchSwapMap σ)).comp
    (squareZeroTwoBranchFactor σ e (parameter_pow R π 1)
      (arithmeticFirstChangedSmoothing_annihilated data H j hj u hu) q).toAlgHom)
  rw [squareZeroTwoBranchFactor_boundary, ← AlgHom.comp_assoc]
  change _ = ((invert.toAlgHom.comp
    ((LaurentSquareZeroAutomorphism.subst e (parameter_pow R π 1)
      (reciprocalField (nonpositivePart (q b)))).comp invert.toAlgHom)).comp
        (LaurentSquareZeroAutomorphism.subst e (parameter_pow R π 1)
          (positivePart (q b)))).comp _
  rw [LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_involutive,
    LaurentSquareZeroAutomorphism.subst_comp,
    show nonpositivePart (q b) + positivePart (q b) = q b from
      (add_comm _ _).trans (parts_add (q b))]

/-- Every retained correction fixes its original opposite puncture exactly. -/
theorem arithmeticFirstResidualRetainedFactor_opposite (b : Bool) :
    ((leftLaurentMap τ).comp (branchSwapMap τ)).comp
        (arithmeticFirstResidualRetainedFactor hπ data H j hj u hu b).toAlgHom =
      (leftLaurentMap τ).comp (branchSwapMap τ) :=
  squareZeroReciprocalFactor_right ..

end FLT.Mazur.WeierstrassDividedDepth
