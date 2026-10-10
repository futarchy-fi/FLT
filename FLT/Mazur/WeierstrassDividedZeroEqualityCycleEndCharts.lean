/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalZeroExteriorRanges
public import FLT.Mazur.WeierstrassDividedZeroEqualityCycle

/-!
# Original exterior and terminal atlas restrictions at equality depth

The full infinity and Laurent charts factor through the actual cyclic components.
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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "ι" => zeroRetainedExteriorInfinityChart hπ data D 0 (by omega) s
  (by omega) (by omega) (by omega)
local notation "E" => zeroRetainedExteriorOrientedIso hπ data D 0 (by omega) s
  (by omega) (by omega) (by omega)
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp

/-- The complete original infinity tensor chart factors through cyclic component zero. -/
@[reassoc] theorem zeroEqualityCycleComponent_infinity_chart :
    ι ≫ (E).hom ≫ (Z 0).left = finiteInfinityTensorChart hπ data K (s + 1) hs := by
  rw [zeroEqualityCycleComponent_exterior]
  change ι ≫ (E).hom ≫ finalZeroExteriorComponent hπ data D s hs hstart hk = _
  rw [finalZeroExteriorComponent, zeroRetainedOrientedToGlobal, Category.assoc,
    Iso.hom_inv_id_assoc,
    zeroRetainedExteriorToGlobal_infinity_assoc,
    finiteInfinityTensorChart_index_transport hπ data _ hs (by omega)]

/-- The whole original Laurent chart factors through the reversed terminal component. -/
@[reassoc] theorem zeroEqualityCycleComponent_terminal_chart :
    ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
        (ProjectiveLine.endpointReversalIso K).inv ≫ (Z ⟨s + 1, by omega⟩).left =
      terminalLaurentChart hπ data D (s + 1) hs (by omega) hk hp := by
  rw [zeroEqualityCycleComponent_terminal]
  change ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
    (ProjectiveLine.endpointReversalIso K).inv ≫
      (ProjectiveLine.endpointReversalIso K).hom ≫
        laurentTerminalProjectiveComponent hπ data D s hs hk hp = _
  rw [Iso.inv_hom_id_assoc, laurentTerminalProjectiveComponent_torus]

variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (zeroEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (zeroEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- Cyclic component agreement determines the original infinity chart into any scheme. -/
theorem zeroEqualityCycleComponent_infinity_hom_ext :
    globalTensorAtlasMap hπ data K (s + 1) hs 0 ≫ f =
      globalTensorAtlasMap hπ data K (s + 1) hs 0 ≫ g := by
  change finiteInfinityTensorChart hπ data K (s + 1) hs ≫ f =
    finiteInfinityTensorChart hπ data K (s + 1) hs ≫ g
  have H := congrArg (fun q => ι ≫ (E).hom ≫ q) (h 0)
  simpa only [zeroEqualityCycleComponent_infinity_chart_assoc] using H

include h in
/-- The original redundant initial atlas chart is also determined by cyclic components. -/
theorem zeroEqualityCycleComponent_initial_hom_ext :
    globalTensorAtlasMap hπ data K (s + 1) hs ⟨s + 3, by omega⟩ ≫ f =
      globalTensorAtlasMap hπ data K (s + 1) hs ⟨s + 3, by omega⟩ ≫ g := by
  change globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ ⟨s + 1 + 1, by omega⟩) ≫ f =
    globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ ⟨s + 1 + 1, by omega⟩) ≫ g
  apply (cancel_epi (initialZeroSlopeAtlasIso hπ data D (by omega)
    hstart (s + 1) hs).hom).mp
  simp only [initialZeroSlopeAtlasIso_map_assoc]
  have H := zeroEqualityCycleComponent_infinity_hom_ext hπ data D s hs hstart hk hp f g h
  have H' := congrArg (fun q =>
    initialZeroToTensorInfinity hπ data D (by omega) hstart (s + 1) hs ≫ q) H
  change initialZeroToTensorInfinity _ _ _ _ _ _ _ ≫
    finiteInfinityTensorChart _ _ _ _ _ ≫ f =
      initialZeroToTensorInfinity _ _ _ _ _ _ _ ≫
        finiteInfinityTensorChart _ _ _ _ _ ≫ g at H'
  simpa only [initialZeroToTensorInfinity_chart_assoc] using H'

include h in
/-- The terminal component determines the entire original Laurent atlas chart. -/
theorem zeroEqualityCycleComponent_terminal_hom_ext :
    globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0) ≫ f =
      globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0) ≫ g := by
  apply (cancel_epi (terminalLaurentAtlasIso hπ data D (s + 1) hs (by omega) hk hp).hom).mp
  simp only [terminalLaurentAtlasIso_map_assoc]
  have H := congrArg (fun q => ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
    (ProjectiveLine.endpointReversalIso K).inv ≫ q) (h ⟨s + 1, by omega⟩)
  simpa only [zeroEqualityCycleComponent_terminal_chart_assoc] using H

end FLT.Mazur.WeierstrassDividedDepth
