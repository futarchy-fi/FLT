/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitPolygonIso
public import FLT.Mazur.SchemeOpenChartRange

/-!
# The strict polygon comparison preserves the independently constructed full exterior

The exterior is the original curve obtained from the incidence line and
infinity chart. Its complete map is retained by the polygon isomorphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
local notation "N" => positiveSplitCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => positiveSplitCycleNodes hπ data D s hs hstart hk hp
local notation "E" => initialExteriorOrientedIso hπ data D (s + 1) hs hstart
  (by omega) (by omega)
local notation "I" => positiveSplitCyclePolygonIso hπ data D s hs hstart hk hp
local notation "C" => PolygonPinching.componentι K (2 * s + 5) 0 ≫
  PolygonAtlas.normalization K (2 * s + 5)

/-- The whole original exterior map is preserved, including both affine gluing charts. -/
@[reassoc] theorem positiveSplitCyclePolygonIso_original_exterior :
    (E).hom ≫ (C).left ≫ (I).hom.left =
      initialExteriorToGlobal hπ data D (s + 1) hs hstart (by omega) := by
  have h := congrArg Over.Hom.left
    (positiveSplitCyclePolygonIso_component hπ data D s hs hstart hk hp 0)
  simp only [Over.comp_left, Category.assoc] at h ⊢
  rw [h, positiveSplitCycleComponent_exterior, equalityInitialExteriorOverComponent_original]

/-- The polygon exterior has exactly the image of the independently constructed original curve. -/
theorem positiveSplitCyclePolygonIso_exterior_range :
    Set.range ((C).left ≫ (I).hom.left) =
      Set.range (initialExteriorToGlobal hπ data D (s + 1) hs hstart (by omega)) := by
  calc
    _ = Set.range ((E).hom ≫ (C).left ≫ (I).hom.left) :=
      (SchemeOpenChartRange.range_iso_comp E ((C).left ≫ (I).hom.left)).symm
    _ = _ := by
      rw [positiveSplitCyclePolygonIso_original_exterior]
      rfl

end FLT.Mazur.WeierstrassDividedDepth
