/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicOmittedChart
public import FLT.Mazur.ProjectiveLineAffineRigidity

/-!
# The original cubic map is constant on every omitted complete component

Constancy is equality of scheme morphisms, obtained from the actual affine
chart factorization. The same equality holds in the specified closed cubic,
not just after forgetting its coefficient-base morphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "W" => completePointWeierstrassCurve K n h i

/-- Every omitted complete normalization component has a constant original cubic map. -/
theorem closedPointOmitted_original_constant {j : Fin n} (hj : j ≠ i) :
    closedPointComponentToOriginalCubic K n h i j =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫
        closedPointComponentToOriginalCubic K n h i j := by
  have H := ProjectiveLineAffineRigidity.comp_eq_constant K
    (closedPointOmittedAffineMap K n h i hj) (integralCurveChart W 2)
  simpa only [closedPointOmittedAffineMap_inclusion] using H

/-- The actual component morphism into the specified Cartesian closed cubic. -/
def closedPointComponentToCubic (j : Fin n) :
    ProjectiveLine.scheme K ⟶ completePointCubicBaseChange K n h (completeClosedBase K) i :=
  (componentι K n j ≫ p).left ≫ closedPointToCubic K n h i

/-- Forgetting the closed base retains exactly the original component morphism. -/
@[reassoc] theorem closedPointComponentToCubic_fst (j : Fin n) :
    closedPointComponentToCubic K n h i j ≫ pullback.fst _ _ =
      closedPointComponentToOriginalCubic K n h i j := by
  rw [closedPointComponentToCubic, Category.assoc, closedPointToCubic,
    completePointToCubicBaseChange_fst]
  rfl

/-- The component's coefficient morphism is the original projective-line structure map. -/
@[reassoc] theorem closedPointComponentToCubic_snd (j : Fin n) :
    closedPointComponentToCubic K n h i j ≫ pullback.snd _ _ =
      ProjectiveLine.toBase K := by
  rw [closedPointComponentToCubic, Category.assoc, closedPointToCubic,
    completePointToCubicBaseChange_snd]
  exact (componentι K n j ≫ p).w

/-- Constancy retains the actual closed cubic and its specified coefficient field. -/
theorem closedPointOmitted_constant {j : Fin n} (hj : j ≠ i) :
    closedPointComponentToCubic K n h i j =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫
        closedPointComponentToCubic K n h i j := by
  apply pullback.hom_ext
  · simp only [Category.assoc, closedPointComponentToCubic_fst]
    exact closedPointOmitted_original_constant K n h i hj
  · simp only [Category.assoc, closedPointComponentToCubic_snd,
      ProjectiveLine.zero_toBase, Category.comp_id]

/-- The two original branches of an omitted component agree as closed-cubic morphisms. -/
theorem closedPointOmitted_endpoints {j : Fin n} (hj : j ≠ i) :
    ProjectiveLine.zero K ≫ closedPointComponentToCubic K n h i j =
      ProjectiveLine.infinity K ≫ closedPointComponentToCubic K n h i j := by
  conv_rhs => rw [closedPointOmitted_constant K n h i hj]
  rw [ProjectiveLine.infinity_toBase_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
