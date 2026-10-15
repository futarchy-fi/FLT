/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeParameterScaling
public import FLT.Mazur.PolygonCompleteIdentityFirstActionBranchEquiv

/-!
# Original action descent on the complete nilpotent node ideal

The unchanged original action agrees with the prescribed node scaling on
every parameter multiple, unconditionally. Its difference from scaling is
an actual linear map annihilating the reduction kernel. The remaining
coordinate-preservation problem is not assumed or asserted to be solved.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "L" => (S)[T;T⁻¹]
local notation "a" => parameterUnit K
local notation "E" => completeIdentityFirstActionBranchEquiv K n h i

/-- The original full branch action is exactly scaling on the entire nilpotent node ideal. -/
theorem completeIdentityFirstActionBranchEquiv_parameter (z : B) :
    (E) (firstNodeBranchPair (R) ((e) • z)) =
      firstNodeBranchPair (R) (reciprocalScale (e) (a) ((e) • z)) := by
  change (E).toAlgHom _ = _
  rw [completeIdentityFirstActionBranchEquiv_toAlgHom]
  exact firstNodeBranchSubstitution_parameter_scaling (R)
    (completeIdentityFirstActionUnit K n h i)
    (completeIdentityFirstActionReciprocalUnit K n h i) (a)
    (completeIdentityFirstActionUnit_reduction K n h i)
    (completeIdentityFirstActionReciprocalUnit_reduction K n h i) z

/-- Original action descent is unconditional for every function in the reduction kernel. -/
theorem completeIdentityFirstActionBranchEquiv_kernel (z : B)
    (hz : firstNodeReduction (R) z = 0) :
    (E) (firstNodeBranchPair (R) z) =
      firstNodeBranchPair (R) (reciprocalScale (e) (a) z) := by
  obtain ⟨w, rfl⟩ := (firstNodeReduction_zero_iff (R) z).mp hz
  exact completeIdentityFirstActionBranchEquiv_parameter K n h i w

/-- In particular the actual original action preserves all nilpotent node functions. -/
theorem completeIdentityFirstActionBranchEquiv_kernel_mem (z : B)
    (hz : firstNodeReduction (R) z = 0) :
    (E) (firstNodeBranchPair (R) z) ∈ firstNodeBranchSubalgebra (R) := by
  rw [completeIdentityFirstActionBranchEquiv_kernel K n h i z hz]
  exact ⟨_, rfl⟩

/-- The full difference of original action and original scaling on node functions. -/
def completeIdentityFirstActionNodeDefect : (B) →ₗ[S] ((L) × (L)) :=
  ((E).toAlgHom.comp (firstNodeBranchPair (R))).toLinearMap -
    ((firstNodeBranchPair (R)).comp (reciprocalScale (e) (a))).toLinearMap

/-- The difference is taken in the actual full Laurent pair algebra. -/
theorem completeIdentityFirstActionNodeDefect_apply (z : B) :
    completeIdentityFirstActionNodeDefect K n h i z =
      (E) (firstNodeBranchPair (R) z) -
        firstNodeBranchPair (R) (reciprocalScale (e) (a) z) := rfl

/-- The computed original defect kills the whole original reduction kernel. -/
theorem completeIdentityFirstActionNodeDefect_kernel (z : B)
    (hz : firstNodeReduction (R) z = 0) :
    completeIdentityFirstActionNodeDefect K n h i z = 0 := by
  rw [completeIdentityFirstActionNodeDefect_apply,
    completeIdentityFirstActionBranchEquiv_kernel K n h i z hz, sub_self]

/-- The remaining defect depends only on the entire reduced node function, not its chosen lift. -/
theorem completeIdentityFirstActionNodeDefect_eq (z w : B)
    (hzw : firstNodeReduction (R) z = firstNodeReduction (R) w) :
    completeIdentityFirstActionNodeDefect K n h i z =
      completeIdentityFirstActionNodeDefect K n h i w := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply completeIdentityFirstActionNodeDefect_kernel
  rw [(firstNodeReduction (R)).map_sub, hzw, sub_self]

end FLT.Mazur.PolygonInfinitesimalStages
