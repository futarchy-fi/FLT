/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveInitialRootChange

/-!
# Independent companion-root initial components in opposite polygon coordinates

Both initial positions in the explicit opposite coordinates are identified
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
local notation "I" => coefficientShearRootCompanionFinalInitialComponent
  hπ data D s hs hstart hk t b hb ht
local notation "O" => coefficientShearRootStrictPositiveOppositeCoordinates
  hπ data D s hs hstart hk hp t
local notation "PN" => (PolygonAtlas.normalization K (2 * s + 5)).left
include hrt

/-- The first initial polygon position is the whole companion first projective component. -/
@[reassoc] theorem coefficientShearRootStrictPositiveOppositeCoordinates_initialFirst :
    (PolygonPinching.componentι K (2 * s + 5) 1).left ≫ PN ≫ (O).hom =
      ProjectiveLine.endpointReversal K ≫ I 0 := by
  have H := coefficientShearRootStrictPositiveOppositeCoordinates_first
    hπ data D s hs hstart hk hp t 0
  rw [coefficientShearRootStrictPositiveBranchComponent_initial] at H
  change _ = _ ≫ coefficientShearRootFinalInitialComponent
    hπ data D s hs hstart hk 1 ≫ _ at H
  rw [coefficientShearRootCompanionFinalInitial_second_rootChange
    hπ data D s hs hstart hk t b hb ht hrt] at H
  exact H

/-- The second initial polygon position is the whole companion second projective component. -/
@[reassoc] theorem coefficientShearRootStrictPositiveOppositeCoordinates_initialSecond :
    (PolygonPinching.componentι K (2 * s + 5) ⟨2 * s + 4, by omega⟩).left ≫
        PN ≫ (O).hom = I 1 := by
  have H := coefficientShearRootStrictPositiveOppositeCoordinates_second
    hπ data D s hs hstart hk hp t 0
  rw [coefficientShearRootStrictPositiveBranchComponent_initial] at H
  change _ = coefficientShearRootFinalInitialComponent
    hπ data D s hs hstart hk 0 ≫ _ at H
  rw [coefficientShearRootCompanionFinalInitial_first_rootChange
    hπ data D s hs hstart hk t b hb ht hrt] at H
  exact H

end FLT.Mazur.WeierstrassDividedDepth
