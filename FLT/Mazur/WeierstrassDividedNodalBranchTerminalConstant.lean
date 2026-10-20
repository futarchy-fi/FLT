/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalBranchRefinementDepth

/-!
# The terminal constant after the full residual refinement

Divide the first branch constant by its exact residual uniformizer power.
The resulting coefficient is a unit, proved from the original exact node
depth. No unit or output smoothness hypothesis is added to the node data.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {m k : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (hdepth : 3 * k ≤ m)

/-- Remove the full residual depth from the actual first branch constant. -/
def nodalBranchTerminalConstant : R :=
  (nodalBranchRefinement_constant_dvd D d hdepth (le_refl (m - 3 * k))).choose

/-- The terminal quotient retains the exact first branch constant. -/
theorem nodalBranchTerminalConstant_factor :
    nodalBranchConstant D d hdepth = π ^ (m - 3 * k) *
      nodalBranchTerminalConstant D d hdepth :=
  (nodalBranchRefinement_constant_dvd D d hdepth (le_refl (m - 3 * k))).choose_spec

/-- Exact node depth forces the fully divided branch constant to be a unit. -/
theorem nodalBranchTerminalConstant_isUnit :
    IsUnit (nodalBranchTerminalConstant D d hdepth) := by
  rw [← notMem_maximalIdeal]
  intro hb
  apply (nodalBranchConstant_exact_depth D d hdepth).2
  rw [nodalBranchTerminalConstant_factor D d hdepth]
  have hp : π ^ (m - 3 * k) ∈ maximalIdeal R ^ (m - 3 * k) :=
    Ideal.pow_mem_pow (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π) _
  simpa only [pow_succ] using Ideal.mul_mem_mul hp hb

omit D d hdepth [IsDomain R] [IsLocalRing R] in
/-- The unconsumed input scale is a positive uniformizer power below quadruple depth. -/
theorem nodalBranchIntermediate_scale_factor (hm : m < 4 * k) :
    π ^ k = π ^ (m - 3 * k) * π ^ (k - (m - 3 * k)) := by
  rw [← pow_add, Nat.add_sub_of_le (by omega : m - 3 * k ≤ k)]

omit D d hdepth [IsDomain R] [IsLocalRing R] in
/-- Every nodal specialization kills the unconsumed input scale. -/
theorem nodalBranchIntermediate_scale_zero (hm : m < 4 * k)
    {T : Type*} [CommRing T] (f : R →+* T) (hπ : f π = 0) :
    f (π ^ (k - (m - 3 * k))) = 0 := by
  rw [map_pow, hπ, zero_pow (by omega : k - (m - 3 * k) ≠ 0)]

end FLT.Mazur.WeierstrassDividedDepth
