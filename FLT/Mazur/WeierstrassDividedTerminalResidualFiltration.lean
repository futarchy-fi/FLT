/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalResidualAlgebra
public import FLT.Mazur.PolygonArithmeticParameterAnnihilator
public import FLT.Mazur.LaurentCoefficientDivisibility

/-!
# The coefficient filtration of the actual residual terminal substitution

Over the original integral domain, the weighted identity detects divisibility
of every Laurent coefficient. Thus the full residual error raises the parameter
filtration, and its first-order coordinate is a square-zero perturbation.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages LaurentPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π (m + 1)
local notation "L" => Q[T;T⁻¹]
local notation "p" => parameter R π (m + 1)
local notation "D" => arithmeticTerminalResidualEquiv data H (m + 1) j hj u hu

include hπ

/-- Every coefficient of the full residual error is divisible by the original parameter. -/
theorem arithmeticTerminalResidual_coeff_dvd (b : Bool) (z : L) (k : ℤ) :
    p ∣ (D b z - z).coeff k := by
  have hw := arithmeticTerminalResidualEquiv_weighted data H (m + 1) j hj u hu
    (p ^ (m + 1)) (by rw [← pow_succ, parameter_pow]) b z
  have hz : C (p ^ (m + 1)) * (D b z - z) = 0 := by
    rw [mul_sub, hw, sub_self]
  have hc := congrArg (fun f : L ↦ f.coeff k) hz
  rw [← smul_eq_C_mul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at hc
  change p ^ (m + 1) * (D b z - z).coeff k = 0 at hc
  obtain ⟨w, hw⟩ := (parameter_last_mul_eq_zero_iff R π hπ m _).mp hc
  exact ⟨w, hw.symm⟩

/-- A single finite Laurent polynomial realizes the entire parameter-divisible error. -/
theorem arithmeticTerminalResidual_dvd (b : Bool) (z : L) : C p ∣ D b z - z :=
  LaurentCoefficientDivisibility.C_dvd_of_coeff p _
    (arithmeticTerminalResidual_coeff_dvd hπ data H m j hj u hu b z)

/-- The actual residual lies in the extended principal coefficient ideal on every input. -/
theorem arithmeticTerminalResidual_sub_mem (b : Bool) (z : L) :
    D b z - z ∈ (ideal Q p).map (algebraMap Q L) := by
  change _ ∈ (Ideal.span {p}).map (algebraMap Q L)
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  exact arithmeticTerminalResidual_dvd hπ data H m j hj u hu b z

/-- The full substitution raises the coefficient filtration by one, including inverse terms. -/
theorem arithmeticTerminalResidual_error_mem_power (b : Bool) (k : ℕ) (z : L)
    (hz : z ∈ ((ideal Q p).map (algebraMap Q L)) ^ k) :
    D b z - z ∈ ((ideal Q p).map (algebraMap Q L)) ^ (k + 1) :=
  NilpotentAlgebraAutomorphism.error_mem_power (ideal Q p) (D b).toAlgHom
    (arithmeticTerminalResidual_sub_mem hπ data H m j hj u hu b) k z hz

/-- Each actual coordinate has a finite Laurent error, without choosing a residue-field lift. -/
theorem arithmeticTerminalResidual_coordinate (b : Bool) :
    ∃ q : L, D b (T 1) = T 1 + C p * q := by
  obtain ⟨q, hq⟩ := arithmeticTerminalResidual_dvd hπ data H m j hj u hu b (T 1)
  exact ⟨q, by linear_combination hq⟩

end FLT.Mazur.WeierstrassDividedDepth
