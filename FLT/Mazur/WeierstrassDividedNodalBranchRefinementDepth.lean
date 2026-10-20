/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalBranchCoefficients
public import FLT.Mazur.WeierstrassNodalDividedDepth

/-!
# Available strict-branch refinement depths

The exact residual constant depth supplies every intermediate scale up to
min(k, m - 3k). The resulting output depth k + r is available from the
original coefficients, including the nonterminal range 3k < m < 4k.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {m k r : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (hdepth : 3 * k ≤ m)
  (hrk : r ≤ k) (hrm : r ≤ m - 3 * k)

include D hdepth hrk in
/-- Every proposed intermediate scale divides the actual third input coefficient. -/
theorem nodalBranchRefinement_third_dvd : π ^ r ∣ d.b3 := by
  have h := (divided_linear_deep_mem D d (by omega)).1
  have h' : d.b3 ∈ maximalIdeal R ^ r := Ideal.pow_le_pow_right (by omega) h
  rwa [D.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h'

include hrm in
/-- Exact remaining constant depth supplies the required first-quotient divisibility. -/
theorem nodalBranchRefinement_constant_dvd :
    π ^ r ∣ nodalBranchConstant D d hdepth := by
  have h := (nodalBranchConstant_exact_depth D d hdepth).1
  have h' : nodalBranchConstant D d hdepth ∈ maximalIdeal R ^ r :=
    Ideal.pow_le_pow_right hrm h
  rwa [D.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h'

omit [IsDomain R] in
/-- The original node coefficients construct the actual intermediate target chart. -/
def nodalBranchRefinementData : Data W π (k + r) :=
  (nodalDepth_exists_data D.maximalIdeal_eq (by omega : 2 * (k + r) ≤ m)
    D.a₃_mem D.a₄_mem D.a₆_mem).some

/-- The largest directly available first refinement step. -/
def nodalBranchRefinementStep (m k : ℕ) : ℕ := min k (m - 3 * k)

/-- The refinement step never exceeds the original input depth. -/
theorem nodalBranchRefinementStep_le_input : nodalBranchRefinementStep m k ≤ k :=
  Nat.min_le_left _ _

/-- The refinement step never exceeds the exact remaining constant depth. -/
theorem nodalBranchRefinementStep_le_residual :
    nodalBranchRefinementStep m k ≤ m - 3 * k := Nat.min_le_right _ _

/-- Every positive-depth nonterminal branch makes strict depth progress. -/
theorem nodalBranchRefinementStep_pos (hk : 0 < k) (hm : 3 * k < m) :
    0 < nodalBranchRefinementStep m k := by
  unfold nodalBranchRefinementStep
  omega

/-- Below quadruple depth the step is exactly the remaining constant depth. -/
theorem nodalBranchRefinementStep_of_le_four (hm : m ≤ 4 * k) :
    nodalBranchRefinementStep m k = m - 3 * k := by
  unfold nodalBranchRefinementStep
  omega

/-- At or above quadruple depth the first step doubles the input depth. -/
theorem nodalBranchRefinementStep_of_four_le (hm : 4 * k ≤ m) :
    nodalBranchRefinementStep m k = k := by
  unfold nodalBranchRefinementStep
  omega

/-- The target constant retains the exact residual depth after the constructed step. -/
theorem nodalBranchRefinementData_exact_depth :
    (nodalBranchRefinementData D hdepth hrk hrm).b6 ∈
        maximalIdeal R ^ (m - 2 * (k + r)) ∧
      (nodalBranchRefinementData D hdepth hrk hrm).b6 ∉
        maximalIdeal R ^ (m - 2 * (k + r) + 1) :=
  divided_constant_exact_depth D _ (by omega)

end FLT.Mazur.WeierstrassDividedDepth
