/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroExteriorCoverage
public import FLT.Mazur.WeierstrassDividedFinalAdjacentOverComponents

/-!
# The actual start-zero exterior in the fixed final node family

The original exterior is transported only along equality of stage indices.
Its ordered endpoints are the first retained pair, over the residue field.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (a := 0 + 1 + s) (b := s + 1) (by omega) hs (by omega))

/-- The complete normalized start-zero exterior in the fixed final model. -/
def finalZeroExteriorComponent :
    ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K (s + 1) hs :=
  zeroRetainedOrientedToGlobal hπ data D 0 (by omega) s (by omega) (by omega)
    (by omega) ≫ transport

/-- The exterior keeps the original coefficient structure after index transport. -/
@[reassoc] theorem finalZeroExteriorComponent_structure :
    finalZeroExteriorComponent hπ data D s hs hstart hk ≫ p = ProjectiveLine.toBase K := by
  rw [finalZeroExteriorComponent, Category.assoc,
    finiteGlobalTensorModel_structure_transport hπ data K _ _ (by omega),
    zeroRetainedOrientedToGlobal_structure]

/-- The exterior is an actual component map over the original residue field. -/
def finalZeroExteriorOverComponent : PolygonPinching.component K ⟶ Over.mk p :=
  Over.homMk (finalZeroExteriorComponent hπ data D s hs hstart hk)
    (finalZeroExteriorComponent_structure hπ data D s hs hstart hk)

variable (hp : 2 * (start + s + 1) < depth)

/-- The first polygon endpoint is exactly the first original retained node. -/
@[reassoc] theorem finalZeroExteriorComponent_zero :
    ProjectiveLine.zero K ≫ finalZeroExteriorComponent hπ data D s hs hstart hk =
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (0, 0))) := by
  have H := retainedNodeSectionAt_index_transport hπ data D
    (a := 0 + 1 + s) (b := s + 1) (by omega) hs (by omega) 0 (by omega) (by omega) 0
  rw [retainedNodeSectionAt_original hπ data D 0 (by omega) s (by omega),
    orderedRetainedSection_zero hπ data D 0 (by omega) s (by omega) (by omega)
      (by omega)] at H
  rw [finalZeroExteriorComponent, ← Category.assoc, zeroRetainedOrientedToGlobal_zero]
  exact H

/-- The opposite polygon endpoint is exactly the second original retained node. -/
@[reassoc] theorem finalZeroExteriorComponent_infinity :
    ProjectiveLine.infinity K ≫ finalZeroExteriorComponent hπ data D s hs hstart hk =
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (0, 1))) := by
  have H := retainedNodeSectionAt_index_transport hπ data D
    (a := 0 + 1 + s) (b := s + 1) (by omega) hs (by omega) 0 (by omega) (by omega) 1
  rw [retainedNodeSectionAt_original hπ data D 0 (by omega) s (by omega),
    orderedRetainedSection_zero hπ data D 0 (by omega) s (by omega) (by omega)
      (by omega)] at H
  rw [finalZeroExteriorComponent, ← Category.assoc, zeroRetainedOrientedToGlobal_infinity]
  exact H

/-- The first endpoint equality holds over the residue field. -/
@[reassoc] theorem finalZeroExteriorOverComponent_zero :
    ProjectiveLine.zeroSection K ≫ finalZeroExteriorOverComponent hπ data D s hs hstart hk =
      finalNodeOverSection hπ data D s hs hk hp (.inl (.inr (0, 0))) := by
  apply Over.OverMorphism.ext
  change ProjectiveLine.zero K ≫ finalZeroExteriorComponent hπ data D s hs hstart hk = _
  exact finalZeroExteriorComponent_zero hπ data D s hs hstart hk hp

/-- The second endpoint equality holds over the residue field. -/
@[reassoc] theorem finalZeroExteriorOverComponent_infinity :
    ProjectiveLine.infinitySection K ≫
        finalZeroExteriorOverComponent hπ data D s hs hstart hk =
      finalNodeOverSection hπ data D s hs hk hp (.inl (.inr (0, 1))) := by
  apply Over.OverMorphism.ext
  change ProjectiveLine.infinity K ≫ finalZeroExteriorComponent hπ data D s hs hstart hk = _
  exact finalZeroExteriorComponent_infinity hπ data D s hs hstart hk hp

end FLT.Mazur.WeierstrassDividedDepth
