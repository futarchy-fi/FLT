/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalBoundaryExtension
public import FLT.Mazur.WeierstrassDividedTerminalWeightedReduction
public import FLT.Mazur.PolygonSmoothingBoundaryWeightConstraint

/-!
# The actual arithmetic terminal normalization has a first-order weight obstruction

The full prescribed Laurent substitutions force an explicit equality on the
constructed arithmetic units. Nilpotent corrections and a nonlinear node map
cannot remove this necessary condition over the fixed original smoothing.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "a" => arithmeticTerminalTangentScale data H 1 j hj u hu
local notation "F" => arithmeticTerminalNormalizationBoundary data H 1 j hj u hu

omit j hj u hu in
/-- The full normalized smoothing annihilates the parameter at arithmetic order one. -/
theorem arithmeticFirstSmoothing_mul_parameter : τ * parameter R π 1 = 0 := by
  rw [← arithmeticStartOneQuotient_relation]
  calc
    _ = (parameter R π 1) ^ 2 * (arithmeticStartOneQuotient W H.a1_unit π 1 : Q) := by ring
    _ = 0 := by rw [parameter_pow R π 1, zero_mul]

omit j hj u hu in
/-- The actual normalized smoothing is square zero in the first arithmetic quotient. -/
theorem arithmeticFirstSmoothing_square : τ ^ 2 = 0 := by
  rw [pow_two, ← arithmeticStartOneQuotient_relation W H.a1_unit π 1]
  calc
    _ = (parameter R π 1) ^ 2 * (arithmeticStartOneQuotient W H.a1_unit π 1 : Q) ^ 2 := by
      ring
    _ = 0 := by rw [parameter_pow R π 1, zero_mul]

/-- Compatibility of the actual full inverse boundaries forces their computed product weight. -/
theorem arithmeticTerminalBoundaryCompatible_first_weight
    (h : ArithmeticTerminalBoundaryCompatible data H 1 j hj u hu) :
    (a true : Q) * (a false : Q) * τ = τ := by
  exact boundary_weight_constraint τ
    (arithmeticTerminalNormalizationEquiv data H 1 j hj u hu true).toAlgHom
    (arithmeticTerminalNormalizationEquiv data H 1 j hj u hu false).toAlgHom
    (a true) (a false)
    (arithmeticTerminalNormalization_weighted data H 1 j hj u hu τ
      (arithmeticFirstSmoothing_mul_parameter data H) true (LaurentPolynomial.T 1))
    (arithmeticTerminalNormalization_weighted data H 1 j hj u hu τ
      (arithmeticFirstSmoothing_mul_parameter data H) false (LaurentPolynomial.T (-1))) h.1

/-- Every node map with both original puncture squares must obey the same first-order equation. -/
theorem arithmeticTerminalExtension_first_weight (N : ChartRing τ →ₐ[Q] ChartRing τ)
    (hl : (leftLaurentMap τ).comp N = F true)
    (hr : ((leftLaurentMap τ).comp (branchSwapMap τ)).comp N = F false) :
    (a true : Q) * (a false : Q) * τ = τ :=
  arithmeticTerminalBoundaryCompatible_first_weight data H j hj u hu
    ((arithmeticTerminalBoundaryCompatible_iff data H 1 j hj u hu).mpr ⟨N, hl, hr⟩)

/-- Failure of the arithmetic weight equation rules out the full simultaneous extension. -/
theorem arithmeticTerminalBoundary_incompatible_of_first_weight
    (h : (a true : Q) * (a false : Q) * τ ≠ τ) :
    ¬ ArithmeticTerminalBoundaryCompatible data H 1 j hj u hu :=
  fun hc ↦ h (arithmeticTerminalBoundaryCompatible_first_weight data H j hj u hu hc)

end FLT.Mazur.WeierstrassDividedDepth
