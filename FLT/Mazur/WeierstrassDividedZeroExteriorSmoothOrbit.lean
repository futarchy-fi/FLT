/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalZeroExterior
public import FLT.Mazur.WeierstrassDividedPositiveEqualityCartesian

/-!
# The split start-zero exterior retains the complete original smooth orbit

The punctured original exterior has the reciprocal Laurent orientation.
Its complete image is the independently retained coefficient smooth cubic.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "E" => finalZeroExteriorComponent hπ data D s hs hstart hk
local notation "B" => finiteGlobalSmoothCoefficientEmbedding K hπ data (s + 1) hs
local notation "hd" => lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk

/-- The actual punctured exterior has exactly the original reciprocal Laurent map. -/
@[reassoc] theorem finalZeroExteriorComponent_laurent :
    ProjectiveLine.overlapRight K ≫ ProjectiveLine.left K ≫ E =
      infinityLaurentChart hπ data D hd (s + 1) hs := by
  rw [← zeroRetainedExteriorOrientedIso_laurent_assoc hπ data D 0 (by omega)
    s (by omega) (by omega) (by omega)]
  simp only [finalZeroExteriorComponent, zeroRetainedOrientedToGlobal, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [zeroRetainedExteriorLaurentChart_toGlobal_assoc]
  change infinityLaurentChart hπ data D _ (0 + 1 + s) _ ≫ _ = _
  rw [infinityLaurentChart, Category.assoc,
    finiteInfinityTensorChart_index_transport hπ data _ hs (by omega)]
  rfl

/-- The complete punctured exterior is precisely the independent original smooth orbit. -/
theorem finalZeroExteriorComponent_smoothOrbit_range :
    Set.range ((PolygonPinching.torusToComponent K).left ≫ E) = Set.range B := by
  have hl : (ProjectiveLine.inversion K).hom ≫
      (PolygonPinching.torusToComponent K).left ≫ E =
        infinityLaurentChart hπ data D hd (s + 1) hs := by
    change (ProjectiveLine.inversion K).hom ≫
      (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫ E = _
    simpa only [ProjectiveLine.overlapRight, Category.assoc] using
      finalZeroExteriorComponent_laurent hπ data D s hs hstart hk
  calc
    _ = Set.range ((ProjectiveLine.inversion K).hom ≫
        (PolygonPinching.torusToComponent K).left ≫ E) :=
      ((ProjectiveLine.inversion K).hom.homeomorph.surjective.range_comp _).symm
    _ = Set.range (infinityLaurentChart hπ data D hd (s + 1) hs) := by rw [hl]
    _ = Set.range (finiteInfinityTensorChart hπ data K (s + 1) hs) :=
      infinityLaurentChart_range hπ data D hd (s + 1) hs
    _ = Set.range (positiveEqualityOriginalSmoothMap hπ data D s hs hk) :=
      (positiveEqualityOriginalSmoothMap_range hπ data D s hs hk).symm
    _ = _ := congrArg (fun a : _ ⟶ _ => Set.range a)
      (positiveEqualityOriginalSmoothMap_eq_coefficientEmbedding hπ data D s hs hk)

end FLT.Mazur.WeierstrassDividedDepth
