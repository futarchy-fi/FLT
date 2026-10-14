/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveRetainedRootChange

/-!
# Independent companion-root retained components in opposite polygon coordinates

Both retained positions in the explicit opposite coordinates are identified
with their independently glued complete projective lines at the companion root.
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
variable (t : ResidueField R) (b : (ResidueField R)ˣ)
  (hb : (b : ResidueField R) =
    (rootShearCurve (W.map (algebraMap R (ResidueField R))) t).a₁)
  (ht : t ^ 2 + algebraMap R (ResidueField R) W.a₁ * t -
    algebraMap R (ResidueField R) W.a₂ = 0)
  (hrt : 0 + t = -algebraMap R (ResidueField R) W.a₁)
variable (j : Fin s)
local notation "I" => coefficientShearRootCompanionFinalAdjacentComponent
  hπ data D s hs hstart hk j t b hb ht
local notation "O" => coefficientShearRootStrictPositiveOppositeCoordinates
  hπ data D s hs hstart hk hp t
local notation "PN" => (PolygonAtlas.normalization K (2 * s + 5)).left
/-- A retained branch level keeps its independent complete adjacent component. -/
theorem coefficientShearRootStrictPositiveBranchComponent_retained (i : Fin 2) :
    coefficientShearRootStrictPositiveBranchComponent hπ data D s hs hstart hk hp
        ⟨j.val + 1, by omega⟩ i =
      coefficientShearRootFinalAdjacentOverComponent hπ data D s hs hk j i := by
  rw [coefficientShearRootStrictPositiveBranchComponent_tail
    hπ data D s hs hstart hk hp ⟨j.val, by omega⟩ i]
  simp only [coefficientShearRootFinalBranchComponent, dite_eq_left j.isLt]

include hrt

/-- Every first retained position is the entire reversed companion first component. -/
@[reassoc] theorem coefficientShearRootStrictPositiveOppositeCoordinates_retainedFirst :
    (PolygonPinching.componentι K (2 * s + 5) ⟨j.val + 2, by omega⟩).left ≫
        PN ≫ (O).hom = ProjectiveLine.endpointReversal K ≫ I 0 := by
  have H := coefficientShearRootStrictPositiveOppositeCoordinates_first
    hπ data D s hs hstart hk hp t ⟨j.val + 1, by omega⟩
  rw [coefficientShearRootStrictPositiveBranchComponent_retained] at H
  change _ = _ ≫ coefficientShearRootFinalAdjacentComponent
    hπ data D s hs hk j 1 ≫ _ at H
  rw [coefficientShearRootCompanionFinalAdjacent_second_rootChange
    hπ data D s hs hstart hk j t b hb ht hrt] at H
  exact H

/-- Every second retained position is the entire companion second component. -/
@[reassoc] theorem coefficientShearRootStrictPositiveOppositeCoordinates_retainedSecond :
    (PolygonPinching.componentι K (2 * s + 5) ⟨2 * s + 3 - j.val, by omega⟩).left ≫
        PN ≫ (O).hom = I 1 := by
  have H := coefficientShearRootStrictPositiveOppositeCoordinates_second
    hπ data D s hs hstart hk hp t ⟨j.val + 1, by omega⟩
  rw [coefficientShearRootStrictPositiveBranchComponent_retained] at H
  change _ = coefficientShearRootFinalAdjacentComponent
    hπ data D s hs hk j 0 ≫ _ at H
  rw [coefficientShearRootCompanionFinalAdjacent_first_rootChange
    hπ data D s hs hstart hk j t b hb ht hrt] at H
  simpa only [Fin.val_mk, show 2 * s + 4 - (j.val + 1) = 2 * s + 3 - j.val by omega]
    using H

end FLT.Mazur.WeierstrassDividedDepth
