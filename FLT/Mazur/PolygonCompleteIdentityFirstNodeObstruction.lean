/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstActionParameter
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The actual original-action obstruction on the reduced node

The full action-minus-scaling defect factors through the reduced node,
because the unchanged action already agrees with scaling on the entire
parameter ideal. Quotienting its values by actual node functions constructs
an additive obstruction whose vanishing is exactly original action descent.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentFirstStageParameter PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)
local notation "L" => (S)[T;T⁻¹]
local notation "D" => completeIdentityFirstActionNodeDefect K n h i
local notation "E" => completeIdentityFirstActionBranchEquiv K n h i

/-- The unchanged full defect, now defined on actual reduced-node functions. -/
def completeIdentityFirstReducedDefect : (N) →+ ((L) × (L)) where
  toFun z := (D) (firstNodeFunctionLift (R) z)
  map_zero' := completeIdentityFirstActionNodeDefect_kernel K n h i _
    (firstNodeFunctionLift_reduction (R) 0)
  map_add' z w := by
    calc
      (D) (firstNodeFunctionLift (R) (z + w)) =
          (D) (firstNodeFunctionLift (R) z + firstNodeFunctionLift (R) w) := by
        apply completeIdentityFirstActionNodeDefect_eq
        rw [firstNodeFunctionLift_reduction, (firstNodeReduction (R)).map_add,
          firstNodeFunctionLift_reduction, firstNodeFunctionLift_reduction]
      _ = _ := map_add (D) _ _

/-- Any lift computes the same full original defect, not merely the same quotient class. -/
theorem completeIdentityFirstReducedDefect_reduction (z : B) :
    completeIdentityFirstReducedDefect K n h i (firstNodeReduction (R) z) = (D) z := by
  apply completeIdentityFirstActionNodeDefect_eq
  exact firstNodeFunctionLift_reduction (R) _

/-- The full reduced defect is annihilated by the original smoothing parameter. -/
theorem completeIdentityFirstReducedDefect_parameter (z : N) :
    (e) • completeIdentityFirstReducedDefect K n h i z = 0 := by
  change (e) • (D) (firstNodeFunctionLift (R) z) = 0
  rw [← map_smul, completeIdentityFirstActionNodeDefect_apply,
    completeIdentityFirstActionBranchEquiv_parameter, sub_self]

/-- The additive target measures failure of a full branch pair to be an actual node function. -/
abbrev firstNodeBranchObstructionGroup :=
  ((L) × (L)) ⧸ (firstNodeBranchSubalgebra (R)).toSubmodule.toAddSubgroup

/-- The actual original obstruction, without a chosen extension or assumed preservation. -/
def completeIdentityFirstNodeObstruction : (N) →+ firstNodeBranchObstructionGroup K :=
  (QuotientAddGroup.mk' _).comp (completeIdentityFirstReducedDefect K n h i)

/-- Its value on any lifted function is exactly the class of the computed original difference. -/
theorem completeIdentityFirstNodeObstruction_reduction (z : B) :
    completeIdentityFirstNodeObstruction K n h i (firstNodeReduction (R) z) =
      QuotientAddGroup.mk' (firstNodeBranchSubalgebra (R)).toSubmodule.toAddSubgroup ((D) z) := by
  change QuotientAddGroup.mk' _
    (completeIdentityFirstReducedDefect K n h i (firstNodeReduction (R) z)) = _
  rw [completeIdentityFirstReducedDefect_reduction]

/-- The obstruction vanishes exactly when the unchanged image extends across the node. -/
theorem completeIdentityFirstNodeObstruction_eq_zero_iff (z : B) :
    completeIdentityFirstNodeObstruction K n h i (firstNodeReduction (R) z) = 0 ↔
      (E) (firstNodeBranchPair (R) z) ∈ firstNodeBranchSubalgebra (R) := by
  rw [completeIdentityFirstNodeObstruction_reduction,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  change (D) z ∈ firstNodeBranchSubalgebra (R) ↔ _
  rw [completeIdentityFirstActionNodeDefect_apply]
  have hs : firstNodeBranchPair (R)
      (reciprocalScale (e) (parameterUnit K) z) ∈ firstNodeBranchSubalgebra (R) := ⟨_, rfl⟩
  constructor
  · intro hz
    simpa only [sub_add_cancel] using (firstNodeBranchSubalgebra (R)).add_mem hz hs
  · intro hz
    exact (firstNodeBranchSubalgebra (R)).sub_mem hz hs

/-- Vanishing of the additive obstruction is equivalent to full original preservation. -/
theorem completeIdentityFirstNodeObstruction_zero_iff :
    completeIdentityFirstNodeObstruction K n h i = 0 ↔
      ∀ p ∈ firstNodeBranchSubalgebra (R), (E) p ∈ firstNodeBranchSubalgebra (R) := by
  constructor
  · intro he p hp
    obtain ⟨z, rfl⟩ := hp
    apply (completeIdentityFirstNodeObstruction_eq_zero_iff K n h i z).mp
    rw [he]
    rfl
  · intro hp
    apply AddMonoidHom.ext
    intro z
    obtain ⟨w, rfl⟩ := firstNodeReduction_surjective (R) z
    exact (completeIdentityFirstNodeObstruction_eq_zero_iff K n h i w).mpr (hp _ ⟨w, rfl⟩)

/-- Vanishing of this constructed obstruction gives the unchanged original positive-order law. -/
theorem completeIdentityFiniteLaw_one_of_nodeObstruction_zero
    (hz : completeIdentityFirstNodeObstruction K n h i = 0) :
    universalEdgeScaling (Ring K 1) ≫ completeIdentityStageTorus K n h i 1 =
      completeIdentityFiniteOriginalMul K n h i 1 :=
  completeIdentityFiniteLaw_one_of_branch_preservation K n h i
    ((completeIdentityFirstNodeObstruction_zero_iff K n h i).mp hz)

end FLT.Mazur.PolygonInfinitesimalStages
