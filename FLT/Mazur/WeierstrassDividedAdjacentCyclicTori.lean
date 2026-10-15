/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOrderedAdjacentComponents
public import FLT.Mazur.ProjectiveLineEndpointReversal
public import FLT.Mazur.PolygonAtlasSmoothLocus

/-!
# Retained cyclic tori and the original full horizontal lines

The two original projective chains retain the signed tangent scales used in
their gluing. The formulas include the initial scale-one components and all
later retained stages, before any arithmetic reparametrization.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (m : ℕ) (hm : j + 2 + m ≤ n)
local notation "F" => ResidueField R
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "C" => orderedAdjacentComponent hπ data D j hj hk hjNext hkNext m hm
local notation "L₁" => olderGlobalMiddleFirstLine hπ data D (j + 1) hjNext m hm
  (by omega) hkNext
local notation "L₂" => olderGlobalMiddleSecondLine hπ data D (j + 1) hjNext m hm
  (by omega) hkNext

/-- The first full right chart retains its actual reciprocal tangent scale. -/
@[reassoc] theorem orderedAdjacentComponent_first_right :
    ProjectiveLine.right F ≫ C 0 = ProjectiveLine.chartScaling F a⁻¹ ≫ L₁ := by
  by_cases h : 0 < start + j
  · rw [orderedAdjacentComponent_positive hπ data D j hj hk hjNext hkNext m hm h]
    exact adjacentRetainedFirstComponent_right hπ data D j hj h hk hjNext hkNext m hm
  · rw [orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext m hm (by omega)]
    exact adjacentZeroFirstComponent_right hπ data D j hj (by omega) hk hjNext hkNext m hm

/-- The opposite full right chart retains the signed reciprocal tangent scale. -/
@[reassoc] theorem orderedAdjacentComponent_second_right :
    ProjectiveLine.right F ≫ C 1 = ProjectiveLine.chartScaling F (-a)⁻¹ ≫ L₂ := by
  by_cases h : 0 < start + j
  · rw [orderedAdjacentComponent_positive hπ data D j hj hk hjNext hkNext m hm h]
    exact adjacentRetainedSecondComponent_right hπ data D j hj h hk hjNext hkNext m hm
  · rw [orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext m hm (by omega)]
    exact adjacentZeroSecondComponent_right hπ data D j hj (by omega) hk hjNext hkNext m hm

/-- The reversed first cyclic torus is the actual retained line with inverse tangent scale. -/
@[reassoc] theorem orderedAdjacentComponent_first_cyclicTorus :
    (PolygonPinching.torusToComponent F).left ≫ ProjectiveLine.endpointReversal F ≫ C 0 =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling a⁻¹).toRingHom) ≫
        ProjectiveLine.overlapLeft F ≫ L₁ := by
  change (ProjectiveLine.overlapLeft F ≫ ProjectiveLine.left F) ≫ _ ≫ _ = _
  rw [Category.assoc, ProjectiveLine.left_endpointReversal_assoc,
    orderedAdjacentComponent_first_right, ← Category.assoc,
    ProjectiveLine.overlapLeft_chartScaling, Category.assoc]
  rfl

/-- The unchanged second cyclic torus is the signed reciprocal on its actual retained line. -/
@[reassoc] theorem orderedAdjacentComponent_second_cyclicTorus :
    (PolygonPinching.torusToComponent F).left ≫ C 1 =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal (-a)⁻¹).toRingHom) ≫
        ProjectiveLine.overlapLeft F ≫ L₂ := by
  change (ProjectiveLine.overlapLeft F ≫ ProjectiveLine.left F) ≫ _ = _
  rw [ProjectiveLine.overlap_condition, Category.assoc, orderedAdjacentComponent_second_right]
  rw [← Category.assoc, ← ProjectiveLine.scaledReciprocal_overlap, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
