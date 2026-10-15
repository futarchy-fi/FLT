/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstPairReduction
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphScheme

/-!
# The actual finite original graph reduces onto the original split node

Reduction of every graph element lies in the unchanged reduced node. This
constructs a surjective map, with a square-zero kernel, without assuming
flatness or discarding the kernel in the original correspondence.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)
local notation "E" => completeIdentityFirstErrorAlgebra K n h i
local notation "D" => completeIdentityFirstActionNodeDefect K n h i
local notation "ρ" => firstNodePairReduction (R)
local notation "β₀" => splitNodeBranchPair (R)

/-- Every actual error reduces to zero on both entire branches. -/
theorem completeIdentityFirstActionNodeDefect_reduction (z : B) : (ρ) ((D) z) = 0 :=
  (firstNodePairReduction_zero_iff (R) _).mpr
    (completeIdentityFirstActionNodeDefect_parameter K n h i z)

/-- Every original graph function has an actual reduced node function as its reduction. -/
theorem completeIdentityFirstGraphReduction_mem (z : E) : (ρ) z.val ∈ (β₀).range := by
  obtain ⟨a, b, c, hz⟩ := completeIdentityFirstErrorAlgebra_normalForm K n h i z.val z.property
  rw [hz, map_add, map_add, map_mul, map_mul,
    completeIdentityFirstActionNodeDefect_reduction,
    completeIdentityFirstActionNodeDefect_reduction, mul_zero, mul_zero, add_zero, add_zero]
  obtain ⟨w, hw⟩ := a.property
  change firstNodeBranchPair (R) w = a.val at hw
  rw [← hw, firstNodePairReduction_branch]
  exact ⟨_, rfl⟩

/-- The reduction map on the actual original graph, before quotienting its kernel. -/
def completeIdentityFirstGraphReduction : (E) →+* (N) :=
  (AlgEquiv.ofInjective (β₀) (splitNodeBranchPair_injective (R))).symm.toRingHom.comp
    (((ρ).comp (E).val.toRingHom).codRestrict (β₀).range.toSubring
      (completeIdentityFirstGraphReduction_mem K n h i))

/-- The constructed node reduction is exactly coefficient reduction of the original pair. -/
theorem completeIdentityFirstGraphReduction_pair (z : E) :
    (β₀) (completeIdentityFirstGraphReduction K n h i z) = (ρ) z.val :=
  congrArg Subtype.val
    ((AlgEquiv.ofInjective (β₀) (splitNodeBranchPair_injective (R))).apply_symm_apply _)

/-- The graph reduction agrees with the original source node reduction on every function. -/
theorem completeIdentityFirstGraphReduction_source (z : B) :
    completeIdentityFirstGraphReduction K n h i
      (completeIdentityFirstGraphSource K n h i z) = firstNodeReduction (R) z := by
  apply splitNodeBranchPair_injective (R)
  rw [completeIdentityFirstGraphReduction_pair, completeIdentityFirstGraphSource_apply,
    firstNodePairReduction_branch]

/-- This is a surjection onto the original reduced node, not merely onto its branch image. -/
theorem completeIdentityFirstGraphReduction_surjective :
    Function.Surjective (completeIdentityFirstGraphReduction K n h i) := by
  intro z
  obtain ⟨w, rfl⟩ := firstNodeReduction_surjective (R) z
  exact ⟨completeIdentityFirstGraphSource K n h i w,
    completeIdentityFirstGraphReduction_source K n h i w⟩

/-- Its full kernel is the parameter annihilator inside the actual graph. -/
theorem completeIdentityFirstGraphReduction_zero_iff (z : E) :
    completeIdentityFirstGraphReduction K n h i z = 0 ↔ (e) • z.val = 0 := by
  rw [← (splitNodeBranchPair_injective (R)).eq_iff, map_zero,
    completeIdentityFirstGraphReduction_pair, firstNodePairReduction_zero_iff]

/-- Any two elements of the actual reduction kernel multiply to zero. -/
theorem completeIdentityFirstGraphReduction_kernel_mul (z w : E)
    (hz : completeIdentityFirstGraphReduction K n h i z = 0)
    (hw : completeIdentityFirstGraphReduction K n h i w = 0) : z * w = 0 := by
  apply Subtype.ext
  exact firstNodePair_annihilator_mul (R) z.val w.val
    ((completeIdentityFirstGraphReduction_zero_iff K n h i z).mp hz)
    ((completeIdentityFirstGraphReduction_zero_iff K n h i w).mp hw)

end FLT.Mazur.PolygonInfinitesimalStages
