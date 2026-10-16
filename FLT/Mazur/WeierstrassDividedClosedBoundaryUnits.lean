/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosingTangentConstraint

/-!
# Exact closing units at arithmetic order zero

The coefficient ideal vanishes at this order. The full terminal parameters
and retained closing unit therefore equal their explicit tangent expressions.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => Quotient R π 0
local notation "L" => Q[T;T⁻¹]
local notation "A" => zeroInitialTangentUnit (W.map (algebraMap R Q))
  (H.a1_unit.map (algebraMap R Q))
local notation "T₁" => LaurentUnitPoints.pointUnit (AlgHom.id Q L)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))

omit data H j hj in
/-- The original arithmetic parameter is zero in the actual order-zero quotient. -/
theorem arithmeticClosedParameter_zero : parameter R π 0 = 0 := by
  simpa using parameter_pow R π 0

omit data H j hj in
/-- Its coefficient ideal, including its Laurent extension, really vanishes. -/
theorem arithmeticClosedLaurentIdeal_zero :
    (ideal Q (parameter R π 0)).map (algebraMap Q L) = ⊥ := by
  simp [ideal, arithmeticClosedParameter_zero]

omit j hj in
/-- The prescribed polygon smoothing itself is zero in this original quotient. -/
theorem arithmeticClosedSmoothing_zero :
    arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 0 = 0 := by
  rw [← arithmeticStartOneQuotient_relation, arithmeticClosedParameter_zero, zero_mul]

/-- The last retained unit has its exact reciprocal tangent-power expression. -/
theorem arithmeticClosedRetainedUnit_eq :
    arithmeticRetainedClosingUnit data H 0 (j + 1) hj ⟨j, by omega⟩ =
      Units.map (algebraMap Q L).toMonoidHom (A ^ (2 * (j + 1))) * T₁⁻¹ := by
  simpa using arithmeticRetainedClosingUnit_reduction data H 0 (j + 1) hj
    ⟨j, by omega⟩ (RingHom.id L) (by rw [arithmeticClosedLaurentIdeal_zero]; exact bot_le)

/-- The small terminal puncture has exactly the original positive tangent coefficient. -/
theorem arithmeticClosedTerminalSecondUnit_eq :
    fixedTerminalPolygonSecondBoundaryUnit data 0 j hj H.a1_unit (H.scale j)
      H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) =
        Units.map (algebraMap Q L).toMonoidHom A * T₁⁻¹ := by
  simpa using arithmeticTerminalSecondUnit_reduction data H 0 j hj (RingHom.id L)
    (by rw [arithmeticClosedLaurentIdeal_zero]; exact bot_le)

variable (u : Rˣ) (hu : Data.b6 (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) = π * ↑u)
local notation "v" => arithmeticFixedTerminalUnit π W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu 0

/-- The opposite coefficient includes the sign and the complete terminal normalization unit. -/
def arithmeticClosedTerminalFirstCoefficient : Qˣ := (-1) * v⁻¹ * A

/-- The opposite unit keeps the reciprocal variable and its exact coefficient. -/
theorem arithmeticClosedTerminalFirstUnit_eq :
    fixedTerminalPolygonFirstBoundaryUnit data 0 j hj H.a1_unit (H.scale j)
      H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu =
        Units.map (algebraMap Q L).toMonoidHom
          (arithmeticClosedTerminalFirstCoefficient data H j hj u hu) * T₁⁻¹ := by
  have h := fixedTerminalPolygonFirstBoundaryUnit_add_tangent_mem data 0 j hj
    H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu
  rw [arithmeticClosedLaurentIdeal_zero, Ideal.mem_bot] at h
  apply Units.ext
  change _ = algebraMap Q L (↑((-1 : Qˣ) * v⁻¹ * A) : Q) *
    (↑T₁⁻¹ : L)
  rw [eq_neg_of_add_eq_zero_left h]
  simp only [Units.val_mul, Units.val_neg, Units.val_one, map_mul, map_neg, map_one]
  change -(algebraMap Q L (↑v⁻¹ : Q) *
    (LaurentPolynomial.T (-1) * algebraMap Q L (algebraMap R Q W.a₁))) =
      -1 * algebraMap Q L (↑v⁻¹ : Q) *
        algebraMap Q L (algebraMap R Q W.a₁) * LaurentPolynomial.T (-1)
  ring

end FLT.Mazur.WeierstrassDividedDepth
