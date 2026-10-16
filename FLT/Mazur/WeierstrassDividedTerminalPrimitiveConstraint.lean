/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalFirstOrderConstraint
public import FLT.Mazur.WeierstrassDilatationFirstTerminalWeight
public import FLT.Mazur.PolygonArithmeticParameterAnnihilator

/-!
# The first-order terminal obstruction in the original integral coefficients

Eliminate the chosen normalization unit. Over a domain, compatibility forces
an explicit divisibility condition on the primitive b6 coefficient and a1.
This is a necessary condition, not a replacement hypothesis for a lift.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "A" => zeroInitialTangentUnit (W.map (algebraMap R Q))
  (H.a1_unit.map (algebraMap R Q))
local notation "a" => arithmeticTerminalTangentScale data H 1 j hj u hu
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "v" => arithmeticFixedTerminalUnit π W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu 1

/-- The product-weight equation is exactly a primitive-coefficient equation at order one. -/
theorem arithmeticTerminalFirstWeight_iff_primitive :
    (a true : Q) * (a false : Q) * τ = τ ↔
      parameter R π 1 *
        (algebraMap R Q (u : R) * (algebraMap R Q W.a₁) ^ (4 * (j + 1)) + 1) = 0 := by
  have ht : τ * (A : Q) ^ 2 = parameter R π 1 := by
    rw [← arithmeticStartOneQuotient_relation, arithmeticStartOneQuotient_eq]
    change (parameter R π 1 * (↑A⁻¹ : Q) ^ 2) * (A : Q) ^ 2 = _
    rw [mul_assoc, ← mul_pow, Units.inv_mul, one_pow, mul_one]
  have hv : τ * (v : Q) = parameter R π 1 * algebraMap R Q (u : R) :=
    arithmeticFirstTerminalUnit_weight π W (π ^ (1 + j + 1))
      (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu
  have hh := terminal_weight_iff_primitive A v (A ^ (2 * (j + 1)))
    τ (parameter R π 1) (algebraMap R Q (u : R)) ht hv
  simpa only [arithmeticTerminalTangentScale, arithmeticTerminalTangentCoefficient,
    Bool.false_eq_true, ↓reduceIte, Units.val_pow_eq_pow_val, ← pow_mul,
    show (A : Q) = algebraMap R Q W.a₁ from rfl,
    show 2 * (j + 1) * 2 = 4 * (j + 1) by omega] using hh

/-- Both full boundaries force an equation on the original primitive coefficient. -/
theorem arithmeticTerminalBoundaryCompatible_first_primitive
    (h : ArithmeticTerminalBoundaryCompatible data H 1 j hj u hu) :
    parameter R π 1 *
      (algebraMap R Q (u : R) * (algebraMap R Q W.a₁) ^ (4 * (j + 1)) + 1) = 0 :=
  (arithmeticTerminalFirstWeight_iff_primitive data H j hj u hu).mp
    (arithmeticTerminalBoundaryCompatible_first_weight data H j hj u hu h)

variable [IsDomain R] (hπ : π ≠ 0)
include hπ in
/-- Domain cancellation expresses the obstruction as integral divisibility. -/
theorem arithmeticTerminalBoundaryCompatible_first_divisibility
    (h : ArithmeticTerminalBoundaryCompatible data H 1 j hj u hu) :
    π ∣ (u : R) * W.a₁ ^ (4 * (j + 1)) + 1 := by
  have hh := arithmeticTerminalBoundaryCompatible_first_primitive data H j hj u hu h
  have he : parameter R π 1 ^ 1 *
      Ideal.Quotient.mk _ ((u : R) * W.a₁ ^ (4 * (j + 1)) + 1) = 0 := by
    simpa only [pow_one, map_add, map_mul, map_pow, map_one,
      Ideal.Quotient.algebraMap_eq] using hh
  simpa only [pow_one] using
    (parameter_pow_mul_mk_eq_zero_iff R π hπ 1 1 1 rfl _).mp he

include hπ in
/-- Failure of the original coefficient congruence disproves simultaneous first-order extension. -/
theorem arithmeticTerminalBoundary_incompatible_of_primitive
    (h : ¬ π ∣ (u : R) * W.a₁ ^ (4 * (j + 1)) + 1) :
    ¬ ArithmeticTerminalBoundaryCompatible data H 1 j hj u hu :=
  fun hc ↦ h (arithmeticTerminalBoundaryCompatible_first_divisibility
    data H j hj u hu hπ hc)

end FLT.Mazur.WeierstrassDividedDepth
