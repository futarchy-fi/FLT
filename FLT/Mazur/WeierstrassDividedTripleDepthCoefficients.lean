/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth
public import FLT.Mazur.WeierstrassDividedDepthAvailability

/-!
# Actual branch quotients at exact node depth three times the input depth

The original coefficients supply the fourth and constant quotients needed
by the first branch output. The constant quotient is a unit by exact depth.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (D : SplitNodeDepth W π (3 * k)) (d : Data W π k)

include D in
/-- The fourth coefficient has the scale factor required by the first branch formula. -/
theorem tripleDepth_fourth_dvd : π ^ k ∣ d.b4 := by
  have h := (divided_linear_deep_mem D d (by omega)).2
  have h' : d.b4 ∈ maximalIdeal R ^ k := Ideal.pow_le_pow_right (by omega) h
  rwa [D.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h'

include D in
/-- The constant coefficient has exactly one further input scale. -/
theorem tripleDepth_constant_dvd : π ^ k ∣ d.b6 := by
  have h := (divided_constant_exact_depth D d (by omega)).1
  rw [show 3 * k - 2 * k = k by omega, D.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  exact h

/-- Construct the fourth quotient from its proved divisibility. -/
def tripleDepthFourth : R := (tripleDepth_fourth_dvd D d).choose

/-- Construct the constant quotient from its proved divisibility. -/
def tripleDepthConstant : R := (tripleDepth_constant_dvd D d).choose

/-- The chosen fourth quotient retains the exact original coefficient. -/
theorem tripleDepthFourth_factor : d.b4 = π ^ k * tripleDepthFourth D d :=
  (tripleDepth_fourth_dvd D d).choose_spec

/-- The chosen constant quotient retains the exact original coefficient. -/
theorem tripleDepthConstant_factor : d.b6 = π ^ k * tripleDepthConstant D d :=
  (tripleDepth_constant_dvd D d).choose_spec

/-- Exact node depth makes the constructed terminal branch constant a unit. -/
theorem tripleDepthConstant_isUnit : IsUnit (tripleDepthConstant D d) := by
  rw [← notMem_maximalIdeal]
  intro h
  have he := (divided_constant_exact_depth D d (by omega)).2
  rw [show 3 * k - 2 * k = k by omega] at he
  apply he
  rw [tripleDepthConstant_factor D d]
  have hp : π ^ k ∈ maximalIdeal R ^ k :=
    Ideal.pow_mem_pow (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π) k
  simpa only [pow_succ] using Ideal.mul_mem_mul hp h

include D in
/-- The divided third coefficient vanishes on the base special fiber. -/
theorem tripleDepth_third_mem : d.b3 ∈ maximalIdeal R := by
  have h := (divided_linear_deep_mem D d (by omega)).1
  have h' : d.b3 ∈ maximalIdeal R ^ 1 := Ideal.pow_le_pow_right (by omega) h
  simpa only [pow_one] using h'

/-- A chosen input datum constructs the entire depth-k finite family. -/
def tripleDepthFamily (i : Fin (k + 1)) : Data W π (0 + i.val) :=
  d.truncate (by have h := i.isLt; omega)

end FLT.Mazur.WeierstrassDividedDepth
