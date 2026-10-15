/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphReduction

/-!
# Original coordinate errors inside the actual finite graph

Realize the full action-minus-scaling errors as elements of the graph itself.
Every graph function has a three-term expression with original node
coefficients and the two coordinate errors. All products of errors vanish.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentFirstStageParameter
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityFirstGraphReduction completeIdentityFirstGraphSource
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "E" => completeIdentityFirstErrorAlgebra K n h i
local notation "s" => completeIdentityFirstGraphSource K n h i
local notation "t" => completeIdentityFirstGraphTarget K n h i
local notation "σ" => reciprocalScale (e) (parameterUnit K)
local notation "D" => completeIdentityFirstActionNodeDefect K n h i
/-- Cache the graph's existing ring structure for its actual errors. -/
local instance completeIdentityFirstGraphErrorsCommRing : CommRing (E) := inferInstance

/-- The discrepancy between the original target and scaling, in the actual graph ring. -/
def completeIdentityFirstGraphError (z : B) : E := (t) z - (s) ((σ) z)

/-- The internal error retains precisely the full branch defect, including nilpotents. -/
theorem completeIdentityFirstGraphError_val (z : B) :
    (completeIdentityFirstGraphError K n h i z).val = (D) z := by
  change ((t) z).val - ((s) ((σ) z)).val = _
  rw [completeIdentityFirstGraphTarget_apply, completeIdentityFirstGraphSource_apply,
    completeIdentityFirstActionNodeDefect_apply]

/-- Every internal original error reduces to zero on the whole original node. -/
theorem completeIdentityFirstGraphError_reduction (z : B) :
    completeIdentityFirstGraphReduction K n h i
      (completeIdentityFirstGraphError K n h i z) = 0 := by
  apply splitNodeBranchPair_injective (R)
  rw [completeIdentityFirstGraphReduction_pair, map_zero,
    completeIdentityFirstGraphError_val, completeIdentityFirstActionNodeDefect_reduction]

/-- Any two internal original errors multiply to zero in the unreduced graph. -/
theorem completeIdentityFirstGraphError_mul (z w : B) :
    completeIdentityFirstGraphError K n h i z *
      completeIdentityFirstGraphError K n h i w = 0 :=
  completeIdentityFirstGraphReduction_kernel_mul K n h i _ _
    (completeIdentityFirstGraphError_reduction K n h i z)
    (completeIdentityFirstGraphError_reduction K n h i w)

/-- Three original node functions express every actual graph function using two actual errors. -/
theorem completeIdentityFirstGraphError_normalForm (z : E) :
    ∃ a b c : B, z = (s) a +
      (s) b * completeIdentityFirstGraphError K n h i (leftCoordinate (e)) +
      (s) c * completeIdentityFirstGraphError K n h i (rightCoordinate (e)) := by
  obtain ⟨a, b, c, hz⟩ := completeIdentityFirstErrorAlgebra_normalForm K n h i z.val z.property
  obtain ⟨a', ha⟩ := a.property
  obtain ⟨b', hb⟩ := b.property
  obtain ⟨c', hc⟩ := c.property
  change firstNodeBranchPair (R) a' = a.val at ha
  change firstNodeBranchPair (R) b' = b.val at hb
  change firstNodeBranchPair (R) c' = c.val at hc
  refine ⟨a', b', c', Subtype.ext ?_⟩
  change z.val = ((s) a').val + ((s) b').val * _ + ((s) c').val * _
  rw [completeIdentityFirstGraphSource_apply, completeIdentityFirstGraphSource_apply,
    completeIdentityFirstGraphSource_apply, completeIdentityFirstGraphError_val,
    completeIdentityFirstGraphError_val, ha, hb, hc]
  exact hz

end FLT.Mazur.PolygonInfinitesimalStages
