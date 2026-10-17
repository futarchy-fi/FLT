/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondResidualFields

/-!
# Whole-node factors of the recomputed residual at the second layer

The actual rebased terminal smoothing is annihilated by pi squared. Both
closing residuals therefore factor through one terminal node automorphism
and the complementary retained-node factors, with full Laurent support.
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
local notation "Q" => Quotient R π 2
local notation "L" => Q[T;T⁻¹]
local notation "e" => parameter R π 2 ^ 2
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 2
local notation "s" => arithmeticResidualLiftTerminalSmoothing hπ data H 2 j hj u hu
local notation "q" => arithmeticSecondResidualField hπ data H j hj u hu false
local notation "D" => arithmeticResidualLiftClosingEquiv hπ data H 2 j hj u hu
local notation "he" => nextCorrectionParameter_square R π 1

omit hπ [IsDomain R] j hj u hu in
/-- The original retained smoothing is annihilated by pi squared on the second layer. -/
theorem arithmeticSecondSmoothing_annihilated : e * τ = 0 := by
  rw [← arithmeticStartOneQuotient_relation]
  calc
    _ = parameter R π 2 ^ 3 * (arithmeticStartOneQuotient W H.a1_unit π 2 : Q) := by ring
    _ = 0 := by rw [parameter_pow R π 2, zero_mul]

/-- The actual rebased terminal smoothing retains the same second-layer annihilator. -/
theorem arithmeticSecondResidualSmoothing_annihilated : e * s = 0 := by
  unfold arithmeticResidualLiftTerminalSmoothing twoBranchCorrectionRebasedSmoothing
    arithmeticTerminalChangedSmoothing
  have ht := arithmeticSecondSmoothing_annihilated data H
  generalize (↑(twoBranchCorrectionDriftUnit R π 2
    (arithmeticTerminalIntegralField hπ data H j hj u hu))⁻¹ : Q) = v
  generalize (↑(arithmeticTerminalTangentScale data H 2 j hj u hu true) : Q) = x
  generalize (↑(arithmeticTerminalTangentScale data H 2 j hj u hu false) : Q) = y
  calc
    _ = (v * x * y) * (e * τ) := by ring
    _ = 0 := by rw [ht, mul_zero]

/-- One full terminal node automorphism realizes both second closing fields. -/
def arithmeticSecondResidualTerminalFactor : ChartRing s ≃ₐ[Q] ChartRing s :=
  squareZeroTwoBranchFactor s e he
    (arithmeticSecondResidualSmoothing_annihilated hπ data H j hj u hu) q

/-- The full complementary factor on each retained node at the second layer. -/
def arithmeticSecondResidualRetainedFactor (b : Bool) : ChartRing τ ≃ₐ[Q] ChartRing τ :=
  squareZeroReciprocalFactor τ e he (arithmeticSecondSmoothing_annihilated data H) (q b)

/-- The retained complementary substitution in the original inverse edge coordinate. -/
def arithmeticSecondResidualOverlapFactor (b : Bool) : L ≃ₐ[Q] L :=
  invert.trans ((LaurentSquareZeroAutomorphism.equiv e he
    (reciprocalField (nonpositivePart (q b)))).trans invert)

local notation "F" => arithmeticSecondResidualTerminalFactor hπ data H j hj u hu
local notation "K" => arithmeticSecondResidualOverlapFactor hπ data H j hj u hu

/-- Both complete second closing boundaries factor through the same actual terminal node. -/
theorem arithmeticSecondResidual_boundary (b : Bool) :
    (D b).toAlgHom.comp (if b then leftLaurentMap s
        else (leftLaurentMap s).comp (branchSwapMap s)) =
      (K b).toAlgHom.comp ((if b then leftLaurentMap s
        else (leftLaurentMap s).comp (branchSwapMap s)).comp (F).toAlgHom) := by
  have hd : (D b).toAlgHom = LaurentSquareZeroAutomorphism.subst e he (q b) :=
    arithmeticSecondResidualField_subst hπ data H j hj u hu false b
  rw [hd]
  change _ = (K b).toAlgHom.comp ((if b then leftLaurentMap s
    else (leftLaurentMap s).comp (branchSwapMap s)).comp
      (squareZeroTwoBranchFactor s e he
        (arithmeticSecondResidualSmoothing_annihilated hπ data H j hj u hu) q).toAlgHom)
  rw [squareZeroTwoBranchFactor_boundary, ← AlgHom.comp_assoc]
  change _ = ((invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst e he
    (reciprocalField (nonpositivePart (q b)))).comp invert.toAlgHom)).comp
      (LaurentSquareZeroAutomorphism.subst e he (positivePart (q b)))).comp _
  rw [LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_involutive,
    LaurentSquareZeroAutomorphism.subst_comp,
    show nonpositivePart (q b) + positivePart (q b) = q b from
      (add_comm _ _).trans (parts_add (q b))]

/-- Each complementary retained factor fixes its entire opposite puncture on this layer. -/
theorem arithmeticSecondResidualRetainedFactor_opposite (b : Bool) :
    ((leftLaurentMap τ).comp (branchSwapMap τ)).comp
        (arithmeticSecondResidualRetainedFactor hπ data H j hj u hu b).toAlgHom =
      (leftLaurentMap τ).comp (branchSwapMap τ) :=
  squareZeroReciprocalFactor_right ..

end FLT.Mazur.WeierstrassDividedDepth
