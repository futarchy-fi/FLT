/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitInfinityMap
public import FLT.Mazur.WeierstrassDividedPositiveSplitTerminalMap
public import FLT.Mazur.WeierstrassDividedPositiveSplitLocalDescRecovery
import all FLT.Mazur.WeierstrassDividedPositiveSplitInfinityMap
import all FLT.Mazur.WeierstrassDividedPositiveSplitTerminalMap

/-!
# End-chart descent recovers both original atlas inclusions

The infinity map retains the entire original exterior embedding. The terminal
map retains both original branches, including the smallest five-component cycle.
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
local notation "F" => fun i => Over.Hom.left (Z i)
local notation "w" => positiveSplitCycleComponent_scheme_endpoints hπ data D s hs hstart hk hp

/-- Descent on the actual cyclic family is the entire original infinity chart. -/
theorem positiveSplitCycleInfinityDesc_original :
    positiveSplitCycleInfinityDesc hπ data D s hs hstart hk F =
      globalTensorAtlasMap hπ data K (s + 1) hs 0 := by
  have H := positiveSplitCycleInfinityDesc_eq_restriction
    hπ data D s hs hstart hk hp F (𝟙 _) (Category.comp_id _)
  simpa only [Category.comp_id] using H.symm

/-- Terminal descent on the actual family is the full original terminal atlas inclusion. -/
theorem positiveSplitCycleTerminalDesc_original :
    positiveSplitCycleTerminalDesc hπ data D s hs hk hp F w =
      globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0) := by
  symm
  apply positiveSplitCycleTerminalDesc_unique
  · exact positiveSplitCycleComponent_terminal_first_branch hπ data D s hs hstart hk hp
  · exact positiveSplitCycleComponent_terminal_second_branch hπ data D s hs hstart hk hp

end FLT.Mazur.WeierstrassDividedDepth
