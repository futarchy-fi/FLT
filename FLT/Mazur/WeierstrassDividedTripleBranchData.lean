/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth
public import FLT.Mazur.WeierstrassNodalDividedDepth

/-!
# Branch coefficient quotients at triple depth

Dividing an input ordinate by its own scale only requires the fourth and
sixth divided coefficients to be divisible by that scale. Original node
depth at least three times the input depth supplies these quotients.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R} {k : ℕ}

/-- Coefficient quotients for a branch, with no output coordinates or smoothness fields. -/
structure BranchQuotientData (d : Data W π k) where
  /-- The fourth divided coefficient after one further division by the input scale. -/
  b4 : R
  /-- The constant divided coefficient after one further division by the input scale. -/
  b6 : R
  factor4 : d.b4 = π ^ k * b4
  factor6 : d.b6 = π ^ k * b6

variable [IsDomain R] [IsLocalRing R] {m : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k)

/-- Triple depth constructs both coefficient quotients from the original node conditions. -/
def tripleBranchData (hk : 3 * k ≤ m) : BranchQuotientData d := by
  have h4 := Ideal.pow_le_pow_right (by omega : k ≤ m + 1 - k)
    (divided_linear_deep_mem D d (by omega)).2
  have h6 := Ideal.pow_le_pow_right (by omega : k ≤ m - 2 * k)
    (divided_constant_exact_depth D d (by omega)).1
  rw [D.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h4 h6
  exact ⟨h4.choose, h6.choose, h4.choose_spec, h6.choose_spec⟩

include D in
/-- The fourth quotient still has the full residual depth inherited from the coefficient. -/
theorem branchQuotientData_b4_mem (q : BranchQuotientData d) (hk : 2 * k ≤ m + 1) :
    q.b4 ∈ maximalIdeal R ^ (m + 1 - 2 * k) := by
  apply nodalDepth_cancel D.uniformizer_ne_zero D.maximalIdeal_eq k
  rw [← q.factor4]
  have he : k + (m + 1 - 2 * k) = m + 1 - k := by omega
  rw [he]
  exact (divided_linear_deep_mem D d (by omega)).2

include D in
/-- The constant quotient requires only triple depth, not a doubled input datum. -/
theorem branchQuotientData_b6_mem (q : BranchQuotientData d) (hk : 3 * k ≤ m) :
    q.b6 ∈ maximalIdeal R ^ (m - 3 * k) := by
  apply nodalDepth_cancel D.uniformizer_ne_zero D.maximalIdeal_eq k
  rw [← q.factor6]
  have he : k + (m - 3 * k) = m - 2 * k := by omega
  rw [he]
  exact (divided_constant_exact_depth D d (by omega)).1

end FLT.Mazur.WeierstrassDividedDepth
