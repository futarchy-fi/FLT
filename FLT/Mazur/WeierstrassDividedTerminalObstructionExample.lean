/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalPrimitiveConstraint
public import FLT.Mazur.WeierstrassDividedTerminalExtensionClosed

/-!
# An actual divided cubic whose closed terminal normalization does not lift

For y² + xy = x³ + 3⁵, the two divided depths and their primitive terminal
coefficient satisfy the original atlas hypotheses. Closed compatibility
holds, but order-one compatibility would force 3 to divide 2.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedTerminalObstructionExample
open WeierstrassDividedDepth PolygonArithmeticStages PolygonSmoothing
open WeierstrassModificationX

/-- An integral cubic with unit tangent and primitive terminal constant at depth two. -/
def curve : WeierstrassCurve ℤ where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 243

/-- The obstruction is exhibited by a cubic with nonzero discriminant. -/
theorem discriminant_ne_zero : curve.Δ ≠ 0 := by
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- Both divided stages come from the very same original integral coefficients. -/
def data (i : Fin 2) : Data curve 3 (1 + i.val) where
  b3 := 0
  b4 := 0
  b6 := if i = 0 then 27 else 3
  factor3 := by simp [curve]
  factor4 := by simp [curve]
  factor6 := by fin_cases i <;> norm_num [curve]

/-- Every original arithmetic atlas coefficient hypothesis holds for this cubic. -/
theorem coefficients : ArithmeticAtlasCoefficients data where
  a1_unit := isUnit_one
  scale_div := by norm_num
  a2_div := dvd_zero _
  b3_div _ := dvd_zero _
  b4_div _ := dvd_zero _
  b6_div i := by fin_cases i <;> norm_num [data]

/-- The final divided coefficient is the original uniformizer times the specified unit one. -/
theorem primitive : (data ⟨1, by decide⟩).b6 = (3 : ℤ) * ↑(1 : ℤˣ) := by
  norm_num [data]

/-- The complete closed normalization exists for both original punctures. -/
theorem closed_compatible :
    ArithmeticTerminalBoundaryCompatible data coefficients 0 0 (by decide) 1 primitive :=
  arithmeticTerminalBoundaryCompatible_closed data coefficients 0 (by decide) 1 primitive

/-- The actual first arithmetic quotient fails the required Laurent coefficient tests. -/
theorem first_incompatible :
    ¬ ArithmeticTerminalBoundaryCompatible data coefficients 1 0 (by decide) 1 primitive := by
  apply arithmeticTerminalBoundary_incompatible_of_primitive data coefficients 0
    (by decide) 1 primitive (by norm_num)
  norm_num [curve]

local notation "Q" => Quotient ℤ 3 1
local notation "τ" => arithmeticInitialMobiusSmoothing curve coefficients.a1_unit (3 ^ 1) 3 1
local notation "F" => arithmeticTerminalNormalizationBoundary data coefficients 1 0
  (by decide) 1 primitive

/-- No full node map can retain both exact original first-order terminal squares. -/
theorem no_first_extension :
    ¬ ∃ N : ChartRing τ →ₐ[Q] ChartRing τ,
      (leftLaurentMap τ).comp N = F true ∧
        ((leftLaurentMap τ).comp (branchSwapMap τ)).comp N = F false := by
  intro h
  exact first_incompatible
    ((arithmeticTerminalBoundaryCompatible_iff data coefficients 1 0
      (by decide) 1 primitive).mpr h)

end FLT.Mazur.WeierstrassDividedTerminalObstructionExample
