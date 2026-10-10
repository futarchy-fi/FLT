/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalZeroExteriorRanges
public import FLT.Mazur.WeierstrassDividedZeroSplitCycle

/-!
# The exterior cyclic component detects maps on infinity and the initial chart

The entire original infinity tensor chart factors through the normalized
exterior. Its original slope transition also controls the redundant initial chart.
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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "ι" => zeroRetainedExteriorInfinityChart hπ data D 0 (by omega) s
  (by omega) (by omega) (by omega)
local notation "E" => zeroRetainedExteriorOrientedIso hπ data D 0 (by omega) s
  (by omega) (by omega) (by omega)
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart hk hp

/-- The complete original infinity tensor chart factors through cyclic component zero. -/
@[reassoc] theorem zeroSplitCycleComponent_infinity_chart :
    ι ≫ (E).hom ≫ (Z 0).left = finiteInfinityTensorChart hπ data K (s + 1) hs := by
  rw [zeroSplitCycleComponent_exterior]
  change ι ≫ (E).hom ≫ finalZeroExteriorComponent hπ data D s hs hstart hk = _
  rw [finalZeroExteriorComponent, zeroRetainedOrientedToGlobal, Category.assoc,
    Iso.hom_inv_id_assoc,
    zeroRetainedExteriorToGlobal_infinity_assoc,
    finiteInfinityTensorChart_index_transport hπ data _ hs (by omega)]

variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (zeroSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (zeroSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- Cyclic component agreement determines the original infinity chart into any scheme. -/
theorem zeroSplitCycleComponent_infinity_hom_ext :
    globalTensorAtlasMap hπ data K (s + 1) hs 0 ≫ f =
      globalTensorAtlasMap hπ data K (s + 1) hs 0 ≫ g := by
  change finiteInfinityTensorChart hπ data K (s + 1) hs ≫ f =
    finiteInfinityTensorChart hπ data K (s + 1) hs ≫ g
  have H := congrArg (fun q => ι ≫ (E).hom ≫ q) (h 0)
  simpa only [zeroSplitCycleComponent_infinity_chart_assoc] using H

include h in
/-- The original redundant initial atlas chart is also determined by cyclic components. -/
theorem zeroSplitCycleComponent_initial_hom_ext :
    globalTensorAtlasMap hπ data K (s + 1) hs ⟨s + 3, by omega⟩ ≫ f =
      globalTensorAtlasMap hπ data K (s + 1) hs ⟨s + 3, by omega⟩ ≫ g := by
  change globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ ⟨s + 1 + 1, by omega⟩) ≫ f =
    globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ ⟨s + 1 + 1, by omega⟩) ≫ g
  apply (cancel_epi (initialZeroSlopeAtlasIso hπ data D (by omega)
    hstart (s + 1) hs).hom).mp
  simp only [initialZeroSlopeAtlasIso_map_assoc]
  have H := zeroSplitCycleComponent_infinity_hom_ext hπ data D s hs hstart hk hp f g h
  have H' := congrArg (fun q =>
    initialZeroToTensorInfinity hπ data D (by omega) hstart (s + 1) hs ≫ q) H
  change initialZeroToTensorInfinity _ _ _ _ _ _ _ ≫
    finiteInfinityTensorChart _ _ _ _ _ ≫ f =
      initialZeroToTensorInfinity _ _ _ _ _ _ _ ≫
        finiteInfinityTensorChart _ _ _ _ _ ≫ g at H'
  simpa only [initialZeroToTensorInfinity_chart_assoc] using H'

end FLT.Mazur.WeierstrassDividedDepth
