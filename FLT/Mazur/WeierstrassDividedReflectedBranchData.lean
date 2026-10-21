/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCommonBranchData
public import FLT.Mazur.WeierstrassDividedNodalDepthAvailability

/-!
# Coefficients for reflected-depth output near the terminal stage

At depths k ≤ l with 2*l ≤ m ≤ k+2*l, use common ordinate depth m-2*l.
The exact constant depth supplies a unit, and reflected output depth
m-k-l is available from the original node conditions.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k l m : ℕ} (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hkl : k ≤ l) (hl : 2 * l ≤ m)

/-- The shallower input also admits division at the terminal residual depth. -/
def reflectedLeftBranchData : CommonBranchData d (m - 2 * l) :=
  commonBranchData D d (by omega)

/-- The deeper input admits division at exactly its constant residual depth. -/
def reflectedRightBranchData : CommonBranchData e (m - 2 * l) :=
  commonBranchData D e (by omega)

include D hkl hl in
/-- The original shallower constant has the exact factor needed in reflected Vieta. -/
theorem reflectedBranch_constant_dvd : π ^ (m - 2 * k) ∣ d.b6 := by
  have h := (divided_constant_exact_depth D d (by omega)).1
  rwa [D.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h

/-- Construct the reflected constant quotient from the original node depth. -/
def reflectedBranchConstant : R := (reflectedBranch_constant_dvd D d hkl hl).choose

/-- Its factorization is the full original divided constant, not a residue identity. -/
theorem reflectedBranchConstant_factor :
    d.b6 = π ^ (m - 2 * k) * reflectedBranchConstant D d hkl hl :=
  (reflectedBranch_constant_dvd D d hkl hl).choose_spec

/-- Exact node depth makes the reflected constant quotient a unit. -/
theorem reflectedBranchConstant_isUnit : IsUnit (reflectedBranchConstant D d hkl hl) := by
  rw [← notMem_maximalIdeal]
  intro h
  apply (divided_constant_exact_depth D d (by omega)).2
  rw [reflectedBranchConstant_factor D d hkl hl]
  have hp : π ^ (m - 2 * k) ∈ maximalIdeal R ^ (m - 2 * k) :=
    Ideal.pow_mem_pow (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π) _
  simpa only [pow_succ] using Ideal.mul_mem_mul hp h

/-- The reflected output datum exists even when the sum-depth datum is unavailable. -/
def reflectedBranchOutputData (hm : m ≤ 2 * (k + l)) : Data W π (m - k - l) :=
  (nodalDepth_exists_data D.maximalIdeal_eq (by omega : 2 * (m - k - l) ≤ m)
    D.a₃_mem D.a₄_mem D.a₆_mem).some

/-- The reflected output lies at or before the deeper input in the near-terminal range. -/
theorem reflectedBranchOutput_depth_le (hm : m ≤ k + 2 * l) : m - k - l ≤ l := by
  omega

end FLT.Mazur.WeierstrassDividedDepth
