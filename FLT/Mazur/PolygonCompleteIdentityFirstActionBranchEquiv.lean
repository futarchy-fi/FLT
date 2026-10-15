/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentFirstOrderAutomorphism
public import FLT.Mazur.PolygonCompleteIdentityFirstActionSubalgebra
public import FLT.Mazur.PolygonFirstNodeSubalgebraPreservation

/-!
# The unchanged original action on both entire Laurent branches

The original action defines an automorphism of the product of the two
Laurent algebras before any node-preservation theorem is available.
Forward preservation of the original node subalgebra suffices: the
constructed node inverse then forces inverse preservation as well.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentUnitPoints LaurentBoundaryVectorField
open LaurentFirstStageParameter PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "L" => (S)[T;T⁻¹]
local notation "a" => parameterUnit K
local notation "U" => completeIdentityFirstActionUnit K n h i
local notation "V" => completeIdentityFirstActionReciprocalUnit K n h i
local notation "F" => completeIdentityFirstActionField K n h i

/-- The exact scaled factorization of the original reciprocal unit, with its full field. -/
theorem completeIdentityFirstActionReciprocalUnit_factor :
    (V) = Units.map (C : (S) →+* (L)).toMonoidHom (a)⁻¹ *
      firstOrderCoordinateUnit (reciprocalField (F)) := by
  apply Units.ext
  rw [completeIdentityFirstActionReciprocalUnit_val, completeIdentityFirstActionUnit_reciprocal,
    Units.val_mul, firstOrderCoordinateUnit_val]
  rfl

/-- The original first action is an automorphism of its entire Laurent branch algebra. -/
def completeIdentityFirstActionLaurentEquiv : (L) ≃ₐ[S] (L) :=
  firstOrderScaledLaurentEquiv (a) (F)

/-- The automorphism is substitution by the unchanged original multiplication unit. -/
theorem completeIdentityFirstActionLaurentEquiv_toAlgHom :
    (completeIdentityFirstActionLaurentEquiv K n h i).toAlgHom = evalUnit (U) := by
  rw [completeIdentityFirstActionLaurentEquiv, firstOrderScaledLaurentEquiv_toAlgHom,
    ← completeIdentityFirstActionUnit_factor]

/-- The reciprocal original branch has its full inverse-scaling algebra automorphism. -/
def completeIdentityFirstActionReciprocalEquiv : (L) ≃ₐ[S] (L) :=
  firstOrderScaledLaurentEquiv (a)⁻¹ (reciprocalField (F))

/-- The reciprocal branch automorphism substitutes the same original reciprocal unit. -/
theorem completeIdentityFirstActionReciprocalEquiv_toAlgHom :
    (completeIdentityFirstActionReciprocalEquiv K n h i).toAlgHom = evalUnit (V) := by
  rw [completeIdentityFirstActionReciprocalEquiv, firstOrderScaledLaurentEquiv_toAlgHom,
    ← completeIdentityFirstActionReciprocalUnit_factor]

/-- Both original branch actions together, prior to proving preservation at the node. -/
def completeIdentityFirstActionBranchEquiv : ((L) × (L)) ≃ₐ[S] ((L) × (L)) :=
  AlgEquiv.prodCongr (completeIdentityFirstActionLaurentEquiv K n h i)
    (completeIdentityFirstActionReciprocalEquiv K n h i)

/-- The whole product automorphism is exactly the original pair substitution. -/
theorem completeIdentityFirstActionBranchEquiv_toAlgHom :
    (completeIdentityFirstActionBranchEquiv K n h i).toAlgHom =
      firstNodeBranchSubstitution (R) (U) (V) := by
  change (completeIdentityFirstActionLaurentEquiv K n h i).toAlgHom.prodMap
    (completeIdentityFirstActionReciprocalEquiv K n h i).toAlgHom = _
  rw [completeIdentityFirstActionLaurentEquiv_toAlgHom,
    completeIdentityFirstActionReciprocalEquiv_toAlgHom]
  rfl

variable
  (hp : ∀ p ∈ firstNodeBranchSubalgebra K[T;T⁻¹],
    completeIdentityFirstActionBranchEquiv K n h i p ∈ firstNodeBranchSubalgebra K[T;T⁻¹])

include hp in
/-- Forward preservation of the actual node subalgebra forces preservation by the inverse. -/
theorem completeIdentityFirstActionBranchEquiv_symm_preserves
    (p : (L) × (L)) (hz : p ∈ firstNodeBranchSubalgebra (R)) :
    (completeIdentityFirstActionBranchEquiv K n h i).symm p ∈
      firstNodeBranchSubalgebra (R) := by
  have he := completeIdentityFirstActionBranchEquiv_toAlgHom K n h i
  have hm := (firstNodeBranchSubstitution_preserves_iff (R) (U) (V)).mp
    (fun p hp' ↦ by rw [← he]; exact hp p hp')
  let f := completeIdentityFirstActionSubalgebraNode K n h i hm.1 hm.2
  obtain ⟨z, rfl⟩ := hz
  refine ⟨f.symm z, ?_⟩
  apply (completeIdentityFirstActionBranchEquiv K n h i).injective
  rw [AlgEquiv.apply_symm_apply]
  change (completeIdentityFirstActionBranchEquiv K n h i).toAlgHom _ = _
  rw [he]
  change firstNodeBranchSubstitution (R) (U) (V) (firstNodeBranchPair (R) (f.symm z)) =
    firstNodeBranchPair (R) z
  rw [← firstNodeBranchReconstruct_pair (R) (U) (V) hm.1 hm.2]
  rw [← firstNodeBranchAutomorphism_apply (R) (U) (V) hm.1 hm.2 (a)
    (completeIdentityFirstActionUnit_reduction K n h i)
    (completeIdentityFirstActionReciprocalUnit_reduction K n h i)]
  exact congrArg (firstNodeBranchPair (R)) (f.apply_symm_apply z)

include hp in
/-- The original full branch automorphism needs only forward node preservation to give the law. -/
theorem completeIdentityFiniteLaw_one_of_branch_preservation :
    universalEdgeScaling (Ring K 1) ≫ completeIdentityStageTorus K n h i 1 =
      completeIdentityFiniteOriginalMul K n h i 1 := by
  have he := completeIdentityFirstActionBranchEquiv_toAlgHom K n h i
  have hm := (firstNodeBranchSubstitution_preserves_iff (R) (U) (V)).mp
    (fun p hp' ↦ by rw [← he]; exact hp p hp')
  exact completeIdentityFiniteLaw_one_of_action_subalgebra K n h i hm.1 hm.2

end FLT.Mazur.PolygonInfinitesimalStages
