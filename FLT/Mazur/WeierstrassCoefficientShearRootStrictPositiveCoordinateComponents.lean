/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveCoordinates
public import FLT.Mazur.CyclicPinchingReflectionIndices

/-!
# All original components and nodes in the opposite strict coordinates

Compute the entire exterior and both chains, including the separate terminal
components. The formulas retain their actual original projective parameters.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "O" => coefficientShearRootStrictPositiveOppositeCoordinates
  hπ data D s hs hstart hk hp
local notation "PN" => (PolygonAtlas.normalization K (2 * s + 5)).left
local notation "PJ" => (PolygonAtlas.nodes K (2 * s + 5)).left
local notation "B" => coefficientShearRootStrictPositiveBranchComponent
  hπ data D s hs hstart hk hp
local notation "E" => coefficientShearGluedOverIso hπ data K 0 (s + 1) hs
local notation "ρ" => ProjectiveLine.endpointReversal K
variable (r : ResidueField R)
local notation "C" => coefficientShearRootChange hπ data K 0 r (s + 1) hs

/-- The entire opposite exterior is the reversed original exterior in the chosen-root fiber. -/
@[reassoc] theorem coefficientShearRootStrictPositiveOppositeCoordinates_exterior :
    (PolygonPinching.componentι K (2 * s + 5) 0).left ≫ PN ≫ (O r).hom =
      ρ ≫ (equalityInitialExteriorOverComponent hπ data D s hs hstart hk).left ≫
        (E).inv.left ≫ (C).hom := by
  rw [coefficientShearRootStrictPositiveOppositeCoordinates_component,
    PolygonPinching.reflectIndex_zero,
    coefficientShearRootStrictPositiveCycleComponent_exterior, Over.comp_left, Category.assoc]

/-- Every first-chain position is the reversed full opposite branch at the same level. -/
@[reassoc] theorem coefficientShearRootStrictPositiveOppositeCoordinates_first
    (j : Fin (s + 2)) :
    (PolygonPinching.componentι K (2 * s + 5) ⟨j.val + 1, by omega⟩).left ≫ PN ≫
        (O r).hom = ρ ≫ (B j 1).left ≫ (C).hom := by
  have hi : PolygonPinching.reflectIndex (⟨j.val + 1, by omega⟩ : Fin (2 * s + 5)) =
      ⟨2 * s + 4 - j.val, by omega⟩ := by
    apply Fin.ext
    rw [PolygonPinching.reflectIndex_val _ (by
      intro h; have H := congrArg Fin.val h; dsimp at H; omega)]
    dsimp only
    omega
  rw [coefficientShearRootStrictPositiveOppositeCoordinates_component, hi,
    coefficientShearRootStrictPositiveCycleComponent_second]

/-- Every opposite-chain position is the full first branch with its unchanged parameter. -/
@[reassoc] theorem coefficientShearRootStrictPositiveOppositeCoordinates_second
    (j : Fin (s + 2)) :
    (PolygonPinching.componentι K (2 * s + 5) ⟨2 * s + 4 - j.val, by omega⟩).left ≫ PN ≫
        (O r).hom = (B j 0).left ≫ (C).hom := by
  have hi : PolygonPinching.reflectIndex
      (⟨2 * s + 4 - j.val, by omega⟩ : Fin (2 * s + 5)) = ⟨j.val + 1, by omega⟩ := by
    apply Fin.ext
    rw [PolygonPinching.reflectIndex_val _ (by
      intro h; have H := congrArg Fin.val h; dsimp at H; omega)]
    dsimp only
    omega
  rw [coefficientShearRootStrictPositiveOppositeCoordinates_component, hi,
    coefficientShearRootStrictPositiveCycleComponent_first, Over.comp_left]
  change ρ ≫ (ρ ≫ _) ≫ _ = _
  rw [Category.assoc, ← Category.assoc ρ, ProjectiveLine.endpointReversal_involutive,
    Category.id_comp]

/-- Each original node has precisely the reflected cyclic index in the opposite coordinates. -/
@[reassoc] theorem coefficientShearRootStrictPositiveOppositeCoordinates_node
    (i : Fin (2 * s + 5)) :
    (PolygonPinching.nodeι K (2 * s + 5) i).left ≫ PJ ≫ (O r).hom =
      (finalNodeOverSection hπ data D s hs hk hp
        (positiveSplitCycleNodeIndex start s hstart (PolygonPinching.reflectNodeIndex i))).left ≫
        (E).inv.left ≫ (C).hom := by
  rw [coefficientShearRootStrictPositiveOppositeCoordinates_nodes, ← Category.assoc]
  have H := congrArg Over.Hom.left
    (PolygonPinching.nodeι_reflection K i)
  simp only [Over.comp_left] at H
  rw [H]
  have HJ := congrArg Over.Hom.left
    (coefficientShearRootStrictPositiveNodes_ι hπ data D s hs hstart hk hp
      (PolygonPinching.reflectNodeIndex i))
  simp only [Over.comp_left] at HJ
  rw [← Category.assoc, HJ, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
