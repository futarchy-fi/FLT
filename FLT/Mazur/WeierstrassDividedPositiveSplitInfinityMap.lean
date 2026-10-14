/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitCycleEndCharts

/-!
# The strict positive-start family on the original infinity chart

The full infinity chart factors through the actual exterior component.
These scheme-map equations retain the original coordinates for subsequent descent.
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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 5) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))

/-- The complete infinity chart receives its map from the oriented exterior component. -/
def positiveSplitCycleInfinityDesc : globalTensorAtlasObject hπ data K (s + 1) hs 0 ⟶ Y :=
  let hk0 : 2 * start ≤ depth := (Nat.mul_le_mul_left 2 (by omega)).trans hk
  initialExteriorInfinityChart hπ data D (s + 1) hs hstart hk0 ≫
    (initialExteriorOrientedIso hπ data D (s + 1) hs hstart hk0
      (lt_of_lt_of_le (Nat.mul_pos (by decide) hstart) hk0)).hom ≫ F 0

/-- Every global map with the prescribed exterior has this complete infinity restriction. -/
theorem positiveSplitCycleInfinityDesc_eq_restriction
    (d : finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Y)
    (hd : (Z 0).left ≫ d = F 0) :
    globalTensorAtlasMap hπ data K (s + 1) hs 0 ≫ d =
      positiveSplitCycleInfinityDesc hπ data D s hs hstart hk F := by
  change finiteInfinityTensorChart hπ data K (s + 1) hs ≫ d = _
  rw [← positiveSplitCycleComponent_infinity_chart hπ data D s hs hstart hk hp]
  simp only [Category.assoc, hd, positiveSplitCycleInfinityDesc]

end FLT.Mazur.WeierstrassDividedDepth
