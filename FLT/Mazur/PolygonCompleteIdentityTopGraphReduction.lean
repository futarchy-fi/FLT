/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopPairReduction
public import FLT.Mazur.PolygonCompleteIdentityTopGraphScheme

/-!
# The full higher original graph reduces to its split node

The preceding original action law makes every actual defect reduce to zero.
This yields a retraction onto the unchanged split node without assuming
flatness or killing any element of the original graph.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentStageParameter
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
variable (hm : completeIdentityFiniteMulDefect K n h i m = 0)
local notation "R" => K[T;T⁻¹]
local notation "e" => parameter (R) (m + 1)
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)
local notation "E" => completeIdentityTopGraphAlgebra K n h i m
local notation "D" => completeIdentityTopActionNodeDefect K n h i m
local notation "ρ" => topNodePairReduction (R) m
local notation "β₀" => splitNodeBranchPair (R)
local notation "s" => topNodeGraphSource (R) m
  (completeIdentityTopActionUnit K n h i m)
  (completeIdentityTopActionReciprocalUnit K n h i m)
local notation "t" => topNodeGraphTarget (R) m
  (completeIdentityTopActionUnit K n h i m)
  (completeIdentityTopActionReciprocalUnit K n h i m)
local notation "σ" => reciprocalScale (e) (parameterUnit K (m + 1))
include hm

/-- Every actual higher defect has zero closed value on both whole branches. -/
theorem completeIdentityTopActionNodeDefect_reduction (z : B) : (ρ) ((D) z) = 0 :=
  topNodePairReduction_annihilator (R) m _
    (completeIdentityTopActionNodeDefect_parameter K n h i m hm z)

/-- Every full graph function reduces to an actual function on the unchanged split node. -/
theorem completeIdentityTopGraphReduction_mem (z : E) : (ρ) z.val ∈ (β₀).range := by
  have hz : z.val ∈ completeIdentityTopErrorAlgebra K n h i m := by
    have he := completeIdentityTopErrorAlgebra_eq_graph K n h i m hm
    change z.val ∈ (completeIdentityTopErrorAlgebra K n h i m).restrictScalars
      (Ring (R) (m + 1))
    rw [he]
    exact z.property
  obtain ⟨a, b, c, he⟩ := completeIdentityTopErrorAlgebra_normalForm K n h i m hm z.val hz
  rw [he, map_add, map_add, map_mul, map_mul,
    completeIdentityTopActionNodeDefect_reduction K n h i m hm,
    completeIdentityTopActionNodeDefect_reduction K n h i m hm,
    mul_zero, mul_zero, add_zero, add_zero]
  obtain ⟨w, hw⟩ := a.property
  change stageNodeBranchPair (R) (m + 1) w = a.val at hw
  rw [← hw, topNodePairReduction_branch]
  exact ⟨_, rfl⟩

/-- Closed reduction of the entire original higher graph. -/
def completeIdentityTopGraphReduction : (E) →+* (N) :=
  (AlgEquiv.ofInjective (β₀) (splitNodeBranchPair_injective (R))).symm.toRingHom.comp
    (((ρ).comp (E).val.toRingHom).codRestrict (β₀).range.toSubring
      (completeIdentityTopGraphReduction_mem K n h i m hm))
local notation "r" => completeIdentityTopGraphReduction K n h i m hm

/-- The constructed reduction retains precisely the reductions of both original branches. -/
theorem completeIdentityTopGraphReduction_pair (z : E) : (β₀) ((r) z) = (ρ) z.val :=
  congrArg Subtype.val
    ((AlgEquiv.ofInjective (β₀) (splitNodeBranchPair_injective (R))).apply_symm_apply _)

/-- Original source functions reduce by the unchanged coefficient map. -/
theorem completeIdentityTopGraphReduction_source (z : B) :
    (r) ((s) z) = topNodeReduction (R) m z := by
  apply splitNodeBranchPair_injective (R)
  rw [completeIdentityTopGraphReduction_pair]
  exact topNodePairReduction_branch (R) m z

/-- Every split-node function is attained by the whole graph reduction. -/
theorem completeIdentityTopGraphReduction_surjective : Function.Surjective (r) := by
  intro z
  obtain ⟨w, rfl⟩ := topNodeReduction_surjective (R) m z
  exact ⟨(s) w, completeIdentityTopGraphReduction_source K n h i m hm w⟩

/-- Original target functions reduce to the prescribed reciprocal source scaling. -/
theorem completeIdentityTopGraphReduction_target (z : B) :
    (r) ((t) z) = topNodeReduction (R) m ((σ) z) := by
  apply splitNodeBranchPair_injective (R)
  rw [completeIdentityTopGraphReduction_pair, ← topNodePairReduction_branch]
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact completeIdentityTopActionNodeDefect_reduction K n h i m hm z

end FLT.Mazur.PolygonInfinitesimalStages
