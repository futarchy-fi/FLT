/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphReduction
public import FLT.Mazur.SquareZeroReductionKernel

/-!
# The full nilradical of the actual original node graph

The graph's reduction is exactly the original split node. Its nilradical is
the kernel of the constructed reduction map and has square zero. These
statements retain the possible extra nilpotents beyond the parameter ideal.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra

/-- The original split node over a domain is reduced, by its faithful two-branch embedding. -/
theorem splitNodeBranchPair_isReduced (R : Type) [CommRing R] [IsDomain R] :
    IsReduced (ChartRing (0 : R)) :=
  isReduced_of_injective (splitNodeBranchPair R) (splitNodeBranchPair_injective R)

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "N" => ChartRing (0 : R)
local notation "E" => completeIdentityFirstErrorAlgebra K n h i
local notation "r" => completeIdentityFirstGraphReduction K n h i
/-- The existing graph ring structure, cached for this construction. -/
local instance completeIdentityFirstGraphNilradicalCommRing : CommRing (E) := inferInstance

/-- The exact graph-reduction kernel is its whole nilradical, without replacing the graph. -/
theorem completeIdentityFirstGraphReduction_ker : RingHom.ker (r) = nilradical (E) := by
  let _ := splitNodeBranchPair_isReduced (R)
  exact SquareZeroReductionKernel.ker_eq_nilradical (r)
    (fun z hz ↦ completeIdentityFirstGraphReduction_kernel_mul K n h i z z hz hz)

/-- The reduction of the actual finite graph is canonically the unchanged original split node. -/
def completeIdentityFirstGraphReducedEquiv : (E) ⧸ nilradical (E) ≃+* (N) :=
  (Ideal.quotEquivOfEq (completeIdentityFirstGraphReduction_ker K n h i).symm).trans
    ((r).quotientKerEquivOfSurjective (completeIdentityFirstGraphReduction_surjective K n h i))

/-- This identification sends each original source function to its literal node reduction. -/
theorem completeIdentityFirstGraphReducedEquiv_source (z : ChartRing (e)) :
    completeIdentityFirstGraphReducedEquiv K n h i
      (Ideal.Quotient.mk _ (completeIdentityFirstGraphSource K n h i z)) =
        firstNodeReduction (R) z := by
  change (r).quotientKerEquivOfSurjective
    (completeIdentityFirstGraphReduction_surjective K n h i) (Ideal.Quotient.mk _ _) = _
  rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
  exact completeIdentityFirstGraphReduction_source K n h i z

/-- Membership in the actual graph nilradical is precisely parameter annihilation. -/
theorem completeIdentityFirstGraph_nilpotent_iff (z : E) :
    IsNilpotent z ↔ (e) • z.val = 0 := by
  rw [← mem_nilradical, ← completeIdentityFirstGraphReduction_ker]
  exact completeIdentityFirstGraphReduction_zero_iff K n h i z

/-- All products of graph nilpotents vanish, including the possible extra node discrepancy. -/
theorem completeIdentityFirstGraph_nilpotent_mul (z w : E)
    (hz : IsNilpotent z) (hw : IsNilpotent w) : z * w = 0 := by
  apply completeIdentityFirstGraphReduction_kernel_mul K n h i
  · exact (completeIdentityFirstGraphReduction_zero_iff K n h i z).mpr
      ((completeIdentityFirstGraph_nilpotent_iff K n h i z).mp hz)
  · exact (completeIdentityFirstGraphReduction_zero_iff K n h i w).mpr
      ((completeIdentityFirstGraph_nilpotent_iff K n h i w).mp hw)

end FLT.Mazur.PolygonInfinitesimalStages
