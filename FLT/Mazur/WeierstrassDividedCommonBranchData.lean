/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTripleBranchData

/-!
# Branch coefficients divided by a common shallower scale

For an input at depth l, division by depth k only requires k + 2*l ≤ m.
This supplies the next construction beyond the triple-depth bound on l.
The data contain coefficient identities only, with no assumed output.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R} {k l : ℕ}

/-- Divide just the fourth and sixth coefficients by an independently chosen scale. -/
structure CommonBranchData (d : Data W π l) (k : ℕ) where
  /-- The fourth coefficient quotient. -/
  b4 : R
  /-- The sixth coefficient quotient. -/
  b6 : R
  factor4 : d.b4 = π ^ k * b4
  factor6 : d.b6 = π ^ k * b6

variable [IsDomain R] [IsLocalRing R] {m : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π l)

/-- The node conditions construct common-scale coefficients without triple depth at l. -/
def commonBranchData (hm : k + 2 * l ≤ m) : CommonBranchData d k := by
  have h4 := Ideal.pow_le_pow_right (by omega : k ≤ m + 1 - l)
    (divided_linear_deep_mem D d (by omega)).2
  have h6 := Ideal.pow_le_pow_right (by omega : k ≤ m - 2 * l)
    (divided_constant_exact_depth D d (by omega)).1
  rw [D.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h4 h6
  exact ⟨h4.choose, h6.choose, h4.choose_spec, h6.choose_spec⟩

include D in
/-- The fourth quotient retains its exact residual lower bound. -/
theorem commonBranchData_b4_mem (q : CommonBranchData d k) (hm : k + l ≤ m + 1) :
    q.b4 ∈ maximalIdeal R ^ (m + 1 - l - k) := by
  apply nodalDepth_cancel D.uniformizer_ne_zero D.maximalIdeal_eq k
  rw [← q.factor4]
  have he : k + (m + 1 - l - k) = m + 1 - l := by omega
  rw [he]
  exact (divided_linear_deep_mem D d (by omega)).2

include D in
/-- The sixth quotient retains its residual bound at the weaker mixed depth. -/
theorem commonBranchData_b6_mem (q : CommonBranchData d k) (hm : k + 2 * l ≤ m) :
    q.b6 ∈ maximalIdeal R ^ (m - 2 * l - k) := by
  apply nodalDepth_cancel D.uniformizer_ne_zero D.maximalIdeal_eq k
  rw [← q.factor6]
  have he : k + (m - 2 * l - k) = m - 2 * l := by omega
  rw [he]
  exact (divided_constant_exact_depth D d (by omega)).1

end FLT.Mazur.WeierstrassDividedDepth
