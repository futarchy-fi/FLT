/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityCycle

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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "ι" => initialExteriorInfinityChart hπ data D (s + 1) hs hstart (by omega)
local notation "E" => initialExteriorOrientedIso hπ data D (s + 1) hs hstart
  (by omega) (by omega)
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp

/-- The complete original infinity tensor chart factors through cyclic component zero. -/
@[reassoc] theorem positiveEqualityCycleComponent_infinity_chart :
    ι ≫ (E).hom ≫ (Z 0).left = finiteInfinityTensorChart hπ data K (s + 1) hs := by
  rw [positiveEqualityCycleComponent_exterior,
    equalityInitialExteriorOverComponent_original,
    initialExteriorToGlobal_infinity]

/-- The whole original Laurent chart factors through the reversed terminal component. -/
@[reassoc] theorem positiveEqualityCycleComponent_terminal_chart :
    ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
        (ProjectiveLine.endpointReversalIso K).inv ≫ (Z ⟨s + 2, by omega⟩).left =
      terminalLaurentChart hπ data D (s + 1) hs (by omega) hk hp := by
  rw [positiveEqualityCycleComponent_terminal]
  change ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
    (ProjectiveLine.endpointReversalIso K).inv ≫
      (ProjectiveLine.endpointReversalIso K).hom ≫
        laurentTerminalProjectiveComponent hπ data D s hs hk hp = _
  rw [Iso.inv_hom_id_assoc, laurentTerminalProjectiveComponent_torus]

variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (positiveEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (positiveEqualityCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- Cyclic component agreement determines the original infinity chart into any scheme. -/
theorem positiveEqualityCycleComponent_infinity_hom_ext :
    globalTensorAtlasMap hπ data K (s + 1) hs 0 ≫ f =
      globalTensorAtlasMap hπ data K (s + 1) hs 0 ≫ g := by
  change finiteInfinityTensorChart hπ data K (s + 1) hs ≫ f =
    finiteInfinityTensorChart hπ data K (s + 1) hs ≫ g
  have H := congrArg (fun q => ι ≫ (E).hom ≫ q) (h 0)
  simpa only [positiveEqualityCycleComponent_infinity_chart_assoc] using H

include h in
/-- The terminal component determines the entire original Laurent atlas chart. -/
theorem positiveEqualityCycleComponent_terminal_hom_ext :
    globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0) ≫ f =
      globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0) ≫ g := by
  apply (cancel_epi (terminalLaurentAtlasIso hπ data D (s + 1) hs (by omega) hk hp).hom).mp
  simp only [terminalLaurentAtlasIso_map_assoc]
  have H := congrArg (fun q => ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
    (ProjectiveLine.endpointReversalIso K).inv ≫ q) (h ⟨s + 2, by omega⟩)
  simpa only [positiveEqualityCycleComponent_terminal_chart_assoc] using H

end FLT.Mazur.WeierstrassDividedDepth
