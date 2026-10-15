/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroExteriorSmoothOrbit
public import FLT.Mazur.WeierstrassDividedInfinitySmoothCompatibility

/-!
# The original exterior torus in full smooth cubic coordinates

The normalized exterior has the reciprocal original infinity parameter as a scheme
morphism, including all functions and the original smooth coefficient embedding.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : start + j = 0) (hk : 2 * (start + j + 1) ≤ depth)
local notation "F" => ResidueField R
local notation "hd" => lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk
local notation "torus" => Over.Hom.left (PolygonPinching.torusToComponent F)

/-- The oriented exterior retains the full original infinity map, before stage transport. -/
@[reassoc] theorem zeroRetainedOrientedToGlobal_laurent :
    ProjectiveLine.overlapRight F ≫ ProjectiveLine.left F ≫
        zeroRetainedOrientedToGlobal hπ data D j hj r hr hk0 hk =
      infinityLaurentChart hπ data D hd (j + 1 + r) hr := by
  rw [← zeroRetainedExteriorOrientedIso_laurent_assoc hπ data D j hj r hr hk0 hk]
  simp only [zeroRetainedOrientedToGlobal, Iso.hom_inv_id_assoc]
  exact zeroRetainedExteriorLaurentChart_toGlobal hπ data D j hj r hr hk0 hk

/-- Its standard torus coordinate is exactly the reciprocal original smooth cubic coordinate. -/
@[reassoc] theorem zeroRetainedOrientedToGlobal_torus :
    torus ≫ zeroRetainedOrientedToGlobal hπ data D j hj r hr hk0 hk =
      (ProjectiveLine.inversion F).hom ≫ (infinityResidueSmoothIso D hd).hom ≫
        finiteGlobalSmoothCoefficientEmbedding F hπ data (j + 1 + r) hr := by
  apply (cancel_epi (ProjectiveLine.inversion F).hom).mp
  have H := zeroRetainedOrientedToGlobal_laurent hπ data D j hj r hr hk0 hk
  rw [infinityLaurentChart_eq_smooth_embedding] at H
  change (ProjectiveLine.inversion F).hom ≫
    (ProjectiveLine.overlapLeft F ≫ ProjectiveLine.left F) ≫ _ =
      (ProjectiveLine.inversion F).hom ≫ (ProjectiveLine.inversion F).inv ≫ _
  rw [Iso.hom_inv_id_assoc]
  simpa only [ProjectiveLine.overlapRight, Category.assoc] using H

variable (s : ℕ) (hs : s + 1 ≤ n) (hstart : start = 0)
  (hks : 2 * (start + s + 1) ≤ depth)
local notation "hds" => lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hks

/-- The transported exterior has the same reciprocal coordinate in the actual final model. -/
@[reassoc] theorem finalZeroExteriorComponent_torus :
    torus ≫ finalZeroExteriorComponent hπ data D s hs hstart hks =
      (ProjectiveLine.inversion F).hom ≫ (infinityResidueSmoothIso D hds).hom ≫
        finiteGlobalSmoothCoefficientEmbedding F hπ data (s + 1) hs := by
  apply (cancel_epi (ProjectiveLine.inversion F).hom).mp
  have H := finalZeroExteriorComponent_laurent hπ data D s hs hstart hks
  rw [infinityLaurentChart_eq_smooth_embedding] at H
  change (ProjectiveLine.inversion F).hom ≫
    (ProjectiveLine.overlapLeft F ≫ ProjectiveLine.left F) ≫ _ =
      (ProjectiveLine.inversion F).hom ≫ (ProjectiveLine.inversion F).inv ≫ _
  rw [Iso.hom_inv_id_assoc]
  simpa only [ProjectiveLine.overlapRight, Category.assoc] using H

end FLT.Mazur.WeierstrassDividedDepth
