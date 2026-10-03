/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundle
public import FLT.Mazur.ProjectiveLineMarkedCharts

/-!
# Laurent transition for the marked-point equations and their duals

The two chart equations differ by (-a⁻¹) T⁻¹. Their powers and dual evaluations
retain this unit, including its sign. These are coordinate-ring calculations;
the comparison with restrictions of polygon sheaf sections remains separate.
-/

open Polynomial
open scoped LaurentPolynomial
@[expose] public noncomputable section
namespace FLT.Mazur.ProjectiveLineMarkedTransition
open LaurentPolynomial
variable {K : Type*} [Field K]

/-- The inverse-coordinate change of regular generators, including its scalar sign. -/
def transition (a : Kˣ) : K[T;T⁻¹]ˣ := (PolygonChartScaling.coordinateUnit (-a))⁻¹

/-- The right equation is the left equation multiplied by the explicit Laurent unit. -/
theorem equation_transition (a : Kˣ) :
    invert (toLaurent (X - Polynomial.C (↑a⁻¹ : K))) =
      (transition a : K[T;T⁻¹]) * toLaurent (X - Polynomial.C (a : K)) := by
  simp only [map_sub, toLaurent_X, toLaurent_C, invert_T, invert_C]
  change T (-1) - LaurentPolynomial.C (↑a⁻¹ : K) =
    (LaurentPolynomial.C (↑(-a)⁻¹ : K) * T (-1)) * (T 1 - LaurentPolynomial.C (a : K))
  rw [mul_sub, mul_assoc, ← T_add]
  simp only [neg_add_cancel, T_zero, mul_one, inv_neg, Units.val_neg, map_neg]
  have hc : LaurentPolynomial.C (↑a⁻¹ : K) * LaurentPolynomial.C (a : K) = 1 := by
    rw [← map_mul]
    simp
  have hp : -LaurentPolynomial.C (↑a⁻¹ : K) * T (-1) * LaurentPolynomial.C (a : K) =
      -T (-1) := by
    calc
      _ = -(LaurentPolynomial.C (↑a⁻¹ : K) * LaurentPolynomial.C (a : K)) * T (-1) := by ring
      _ = _ := by rw [hc]; simp
  rw [hp]
  ring

/-- The same generator transition for arbitrary multiplicities. -/
theorem power_transition (a : Kˣ) (m : ℕ) :
    invert (toLaurent ((X - Polynomial.C (↑a⁻¹ : K)) ^ m)) =
      ((transition a : K[T;T⁻¹]) ^ m) * toLaurent ((X - Polynomial.C (a : K)) ^ m) := by
  rw [map_pow, map_pow, equation_transition, mul_pow, map_pow]

/-- The endpoint value of the powered equation is an explicit coefficient unit. -/
theorem endpoint_equation (a : Kˣ) (m : ℕ) :
    eval 0 ((X - Polynomial.C (a : K)) ^ m) = (↑((-a) ^ m : Kˣ) : K) := by
  simp

/-- The right-chart generator belongs to the actual principal Laurent ideal. -/
theorem right_mem_left_ideal (a : Kˣ) (m : ℕ) :
    invert (toLaurent ((X - Polynomial.C (↑a⁻¹ : K)) ^ m)) ∈
      Ideal.span {toLaurent ((X - Polynomial.C (a : K)) ^ m)} := by
  rw [power_transition]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))

/-- Evaluating a functional on the two generators gives the weighted coordinate relation. -/
theorem dual_transition (a : Kˣ) (m : ℕ)
    (f : Module.Dual K[T;T⁻¹] (Ideal.span {toLaurent ((X - Polynomial.C (a : K)) ^ m)})) :
    f ⟨invert (toLaurent ((X - Polynomial.C (↑a⁻¹ : K)) ^ m)), right_mem_left_ideal a m⟩ =
      (transition a : K[T;T⁻¹]) ^ m *
        f ⟨toLaurent ((X - Polynomial.C (a : K)) ^ m),
          Ideal.subset_span (Set.mem_singleton _)⟩ := by
  let x : Ideal.span {toLaurent ((X - Polynomial.C (a : K)) ^ m)} :=
    ⟨_, Ideal.subset_span (Set.mem_singleton _)⟩
  have he : (⟨invert (toLaurent ((X - Polynomial.C (↑a⁻¹ : K)) ^ m)),
      right_mem_left_ideal a m⟩ : Ideal.span {toLaurent ((X - Polynomial.C (a : K)) ^ m)}) =
      (transition a : K[T;T⁻¹]) ^ m • x := by
    apply Subtype.ext
    exact power_transition a m
  rw [he, map_smul]
  rfl
end FLT.Mazur.ProjectiveLineMarkedTransition
