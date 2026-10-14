/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitAtlasFamily
public import FLT.Mazur.WeierstrassDividedPositiveSplitInitialDescRecovery
public import FLT.Mazur.WeierstrassDividedPositiveSplitIndexedDescRecovery
public import FLT.Mazur.WeierstrassDividedPositiveSplitEndDescRecovery
import all FLT.Mazur.WeierstrassDividedPositiveSplitAtlasFamily

/-!
# The strict-cycle atlas family recovers every original chart

For the complete original cyclic component maps, the assembled family equals
the actual indexed atlas map on every chart, including both boundary indices.
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

/-- The constructed local descents retain the entire original indexed atlas family. -/
theorem positiveSplitCycleAtlasFamily_original (i : Fin (s + 1 + 3)) :
    positiveSplitCycleAtlasFamily hπ data D s hs hstart hk hp F w i =
      globalTensorAtlasMap hπ data K (s + 1) hs i := by
  by_cases hzero : i = 0
  · subst i
    rw [positiveSplitCycleAtlasFamily_infinity, positiveSplitCycleInfinityDesc_original]
  by_cases hone : i = Fin.succ 0
  · subst i
    rw [positiveSplitCycleAtlasFamily_terminal, positiveSplitCycleTerminalDesc_original]
  by_cases hlast : i = ⟨s + 3, by omega⟩
  · subst i
    rw [positiveSplitCycleAtlasFamily_initial, positiveSplitInitialIndexedDesc_original]
  have hi0 : i.val ≠ 0 := fun h => hzero (Fin.ext h)
  have hi1 : i.val ≠ 1 := fun h => hone (Fin.ext h)
  have hi3 : i.val ≠ s + 3 := fun h => hlast (Fin.ext h)
  let j : Fin (s + 1) := ⟨s + 2 - i.val, by omega⟩
  have hi : i = ⟨s - j.val + 2, by omega⟩ := by
    apply Fin.ext
    dsimp [j]
    omega
  rw [hi, positiveSplitCycleAtlasFamily_positive, positiveSplitCycleRetainedIndexedDesc_original]

end FLT.Mazur.WeierstrassDividedDepth
