/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityCycleEndCharts

/-!
# The positive-start equality family on both end charts

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
local notation "J" => terminalLaurentAtlasIso hπ data D (s + 1) hs
  (Nat.zero_lt_succ (start + s)) hk hp
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))

/-- The complete infinity chart receives its map from the oriented exterior component. -/
def positiveEqualityCycleInfinityDesc : globalTensorAtlasObject hπ data K (s + 1) hs 0 ⟶ Y :=
  let hk0 : 2 * start ≤ depth := (Nat.mul_le_mul_left 2 (by omega)).trans hk
  initialExteriorInfinityChart hπ data D (s + 1) hs hstart hk0 ≫
    (initialExteriorOrientedIso hπ data D (s + 1) hs hstart hk0
      (lt_of_lt_of_le (Nat.mul_pos (by decide) hstart) hk0)).hom ≫ F 0

/-- Every global map with the prescribed exterior has this complete infinity restriction. -/
theorem positiveEqualityCycleInfinityDesc_eq_restriction
    (d : finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Y)
    (hd : (Z 0).left ≫ d = F 0) :
    globalTensorAtlasMap hπ data K (s + 1) hs 0 ≫ d =
      positiveEqualityCycleInfinityDesc hπ data D s hs hstart hk F := by
  change finiteInfinityTensorChart hπ data K (s + 1) hs ≫ d = _
  rw [← positiveEqualityCycleComponent_infinity_chart hπ data D s hs hstart hk hp]
  simp only [Category.assoc, hd, positiveEqualityCycleInfinityDesc]

/-- The terminal Laurent chart receives the full reversed terminal component map. -/
def positiveEqualityCycleTerminalAtlasDesc :
    globalTensorAtlasObject hπ data K (s + 1) hs (Fin.succ 0) ⟶ Y :=
  (J).inv ≫ ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
    (ProjectiveLine.endpointReversalIso K).inv ≫ F ⟨s + 2, by omega⟩

omit [IsBezout R] in
/-- Pulling back to the actual torus keeps its exact projective parameter. -/
@[reassoc] theorem positiveEqualityCycleTerminalAtlasDesc_torus :
    (J).hom ≫ positiveEqualityCycleTerminalAtlasDesc hπ data D s hs hk hp F =
      ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
        (ProjectiveLine.endpointReversalIso K).inv ≫ F ⟨s + 2, by omega⟩ := by
  simp only [positiveEqualityCycleTerminalAtlasDesc, Iso.hom_inv_id_assoc]

/-- Any global map with the prescribed terminal component has this atlas restriction. -/
theorem positiveEqualityCycleTerminalAtlasDesc_eq_restriction
    (d : finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Y)
    (hd : (Z ⟨s + 2, by omega⟩).left ≫ d = F ⟨s + 2, by omega⟩) :
    globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0) ≫ d =
      positiveEqualityCycleTerminalAtlasDesc hπ data D s hs hk hp F := by
  apply (cancel_epi (J).hom).mp
  rw [positiveEqualityCycleTerminalAtlasDesc_torus, terminalLaurentAtlasIso_map_assoc,
    ← positiveEqualityCycleComponent_terminal_chart hπ data D s hs hstart hk hp]
  simp only [Category.assoc, hd]

end FLT.Mazur.WeierstrassDividedDepth
