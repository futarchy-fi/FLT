/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth
public import FLT.Mazur.WeierstrassDividedDepthAvailability

/-!
# Branch quotients at arbitrary sufficiently deep nodes

A node depth at least three times the input depth supplies actual fourth
and constant branch quotients. The constant quotient has exact remaining
depth n - 3k; it is a unit precisely at triple depth. This identifies when
the first branch output terminates and when a deeper output is still needed.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n k : ℕ}
  (D : SplitNodeDepth W π n) (d : Data W π k) (hdepth : 3 * k ≤ n)

include D hdepth in
/-- The fourth coefficient has the scale factor required by the first branch formula. -/
theorem nodalBranch_fourth_dvd : π ^ k ∣ d.b4 := by
  have h := (divided_linear_deep_mem D d (by omega)).2
  have h' : d.b4 ∈ maximalIdeal R ^ k := Ideal.pow_le_pow_right (by omega) h
  rwa [D.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h'

include D hdepth in
/-- The constant coefficient has at least one further input scale. -/
theorem nodalBranch_constant_dvd : π ^ k ∣ d.b6 := by
  have h := (divided_constant_exact_depth D d (by omega)).1
  have h' : d.b6 ∈ maximalIdeal R ^ k := Ideal.pow_le_pow_right (by omega) h
  rwa [D.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h'

/-- Construct the fourth quotient from its proved divisibility. -/
def nodalBranchFourth : R := (nodalBranch_fourth_dvd D d hdepth).choose

/-- Construct the constant quotient from its proved divisibility. -/
def nodalBranchConstant : R := (nodalBranch_constant_dvd D d hdepth).choose

/-- The chosen fourth quotient retains the exact original coefficient. -/
theorem nodalBranchFourth_factor : d.b4 = π ^ k * nodalBranchFourth D d hdepth :=
  (nodalBranch_fourth_dvd D d hdepth).choose_spec

/-- The chosen constant quotient retains the exact original coefficient. -/
theorem nodalBranchConstant_factor : d.b6 = π ^ k * nodalBranchConstant D d hdepth :=
  (nodalBranch_constant_dvd D d hdepth).choose_spec

/-- The constant branch quotient retains the exact remaining coefficient depth. -/
theorem nodalBranchConstant_exact_depth :
    nodalBranchConstant D d hdepth ∈ maximalIdeal R ^ (n - 3 * k) ∧
      nodalBranchConstant D d hdepth ∉ maximalIdeal R ^ (n - 3 * k + 1) := by
  have hd := divided_constant_exact_depth D d (by omega)
  constructor
  · apply WeierstrassDilatation.divided_mem_power D k (n - 3 * k)
    rw [← nodalBranchConstant_factor D d hdepth]
    simpa only [show k + (n - 3 * k) = n - 2 * k by omega] using hd.1
  · intro hb
    apply hd.2
    rw [nodalBranchConstant_factor D d hdepth]
    have hp : π ^ k ∈ maximalIdeal R ^ k :=
      Ideal.pow_mem_pow (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π) k
    have h := Ideal.mul_mem_mul hp hb
    rw [← pow_add, show k + (n - 3 * k + 1) = n - 2 * k + 1 by omega] at h
    exact h

/-- Exactly triple-depth nodes give a unit first-branch constant quotient. -/
theorem nodalBranchConstant_isUnit_iff : IsUnit (nodalBranchConstant D d hdepth) ↔ n = 3 * k := by
  rw [← notMem_maximalIdeal]
  constructor
  · intro hu
    by_contra hn
    exact hu (Ideal.pow_le_self (by omega) (nodalBranchConstant_exact_depth D d hdepth).1)
  · intro hn
    have h := (nodalBranchConstant_exact_depth D d hdepth).2
    simpa only [hn, Nat.sub_self, Nat.zero_add, pow_one] using h

/-- The fourth quotient retains its full excess linear coefficient depth. -/
theorem nodalBranchFourth_deep_mem :
    nodalBranchFourth D d hdepth ∈ maximalIdeal R ^ (n + 1 - 2 * k) := by
  apply WeierstrassDilatation.divided_mem_power D k (n + 1 - 2 * k)
  rw [← nodalBranchFourth_factor D d hdepth]
  have h := (divided_linear_deep_mem D d (by omega)).2
  simpa only [show k + (n + 1 - 2 * k) = n + 1 - k by omega] using h

end FLT.Mazur.WeierstrassDividedDepth
