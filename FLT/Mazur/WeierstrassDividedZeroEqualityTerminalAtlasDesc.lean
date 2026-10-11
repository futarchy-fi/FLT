/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityCycleEndCharts

/-!
# The equality-cycle family map on the entire original terminal atlas chart

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
local notation "J" => terminalLaurentAtlasIso hπ data D (s + 1) hs
  (Nat.zero_lt_succ (start + s)) hk hp
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart hk hp
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))

/-- The terminal Laurent chart receives the full reversed terminal component map. -/
def zeroEqualityCycleTerminalAtlasDesc :
    globalTensorAtlasObject hπ data K (s + 1) hs (Fin.succ 0) ⟶ Y :=
  (J).inv ≫ ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
    (ProjectiveLine.endpointReversalIso K).inv ≫ F ⟨s + 1, by omega⟩

omit [IsBezout R] in
/-- Pulling back to the actual torus keeps its exact projective parameter. -/
@[reassoc] theorem zeroEqualityCycleTerminalAtlasDesc_torus :
    (J).hom ≫ zeroEqualityCycleTerminalAtlasDesc hπ data D s hs hk hp F =
      ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K ≫
        (ProjectiveLine.endpointReversalIso K).inv ≫ F ⟨s + 1, by omega⟩ := by
  simp only [zeroEqualityCycleTerminalAtlasDesc, Iso.hom_inv_id_assoc]

/-- Any global map with the prescribed terminal component has this atlas restriction. -/
theorem zeroEqualityCycleTerminalAtlasDesc_eq_restriction
    (d : finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Y)
    (hd : (Z ⟨s + 1, by omega⟩).left ≫ d = F ⟨s + 1, by omega⟩) :
    globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0) ≫ d =
      zeroEqualityCycleTerminalAtlasDesc hπ data D s hs hk hp F := by
  apply (cancel_epi (J).hom).mp
  rw [zeroEqualityCycleTerminalAtlasDesc_torus, terminalLaurentAtlasIso_map_assoc,
    ← zeroEqualityCycleComponent_terminal_chart hπ data D s hs hstart hk hp]
  simp only [Category.assoc, hd]

end FLT.Mazur.WeierstrassDividedDepth
