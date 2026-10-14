/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteRotatedEdges
public import FLT.Mazur.PolygonCompleteIdentityFiniteComparison

/-!
# One original Laurent group-law equation controls the whole finite cubic action

The full finite comparison is equivalent to identifying the actual original
identity multiplication in its full Laurent coordinates. Rotation propagates
that equation to every edge; schematic detection then includes all nodes.
The coordinate-law equation itself remains a mathematical theorem to prove.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "U" => completePointIdentityOpen K n h (0 : Fin n)
local notation "e" => completeIdentityStageTorus K n h 0 m
local notation "c" => completePointToIntegralCubic K n h 0

/-- The exact whole-input cubic comparison is equivalent to one actual original coordinate law. -/
theorem completeIdentityFiniteComparison_iff_laurentLaw :
    completeIdentityFiniteScaling K n h m ≫ (c) =
        completeIdentityFiniteInput K n h 0 m ≫ completeIdentityActionTarget K n h 0 ↔
      universalEdgeScaling (A) ≫ (e) = completeIdentityFiniteOriginalMul K n h 0 m := by
  constructor
  · intro he
    apply (completeIdentityFiniteComparison_iff_originalMul K n h 0 m).mp
    exact congrArg (edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h 0 ≫ ·) he
  · intro he
    apply (completeIdentityFiniteComparison_iff_edges K n h m).mpr
    intro i
    let b := ZMod.finEquiv n i
    have hi : rotateIndex b (0 : Fin n) = i := by
      simp only [rotateIndex, map_zero, zero_add, b, RingEquiv.symm_apply_apply]
    rw [← hi, completeIdentityFiniteScaling_rotatedEdge_assoc,
      ← completeIdentityFiniteOriginalMul_rotatedCubic]
    simpa only [Category.assoc] using
      congrArg (fun f ↦ f ≫ (U).ι ≫ completeRotation K n h b ≫ (c)) he

end FLT.Mazur.PolygonInfinitesimalStages
