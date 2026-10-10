/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import all FLT.Mazur.WeierstrassDividedZeroCycleExteriorMaps
import all FLT.Mazur.WeierstrassDividedZeroCycleTerminalMap
import all FLT.Mazur.WeierstrassDividedZeroCycleZeroIndexedMap
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveIndexedMap

public import FLT.Mazur.WeierstrassDividedZeroCycleExteriorMaps
public import FLT.Mazur.WeierstrassDividedZeroCycleTerminalMap
public import FLT.Mazur.WeierstrassDividedZeroCycleZeroIndexedMap
import all FLT.Mazur.WeierstrassDividedZeroCycleLocalMaps
import all FLT.Mazur.WeierstrassDividedZeroCycleAttachmentMaps

/-!
# One cyclic family on the original finite global atlas

All five kinds of original chart receive maps from the same compatible family.
The indexing retains the original order, including the redundant initial chart.
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
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- The chosen cyclic maps form one family on the actual global open cover. -/
def zeroSplitCycleAtlasFamily (i : Fin (s + 1 + 3)) :
    (globalTensorOpenCover hπ data K (s + 1) hs).X i ⟶ Y := by
  by_cases hzero : i = 0
  · subst i
    exact zeroSplitCycleInfinityDesc hπ data D s hs hstart (by omega) F
  by_cases hone : i = Fin.succ 0
  · subst i
    exact zeroSplitCycleTerminalDesc hπ data D s hs (by omega) hp F w
  by_cases hold : i = ⟨s + 2, by omega⟩
  · subst i
    exact zeroSplitCycleZeroIndexedDesc hπ data D s hs hstart hp F w
  by_cases hlast : i = ⟨s + 3, by omega⟩
  · subst i
    exact zeroSplitCycleInitialDesc hπ data D s hs hstart (by omega) F
  have hi0 : i.val ≠ 0 := fun h => hzero (Fin.ext h)
  have hi1 : i.val ≠ 1 := fun h => hone (Fin.ext h)
  have hi2 : i.val ≠ s + 2 := fun h => hold (Fin.ext h)
  have hi3 : i.val ≠ s + 3 := fun h => hlast (Fin.ext h)
  let j : Fin s := ⟨s + 1 - i.val, by omega⟩
  have hi : i = ⟨s - j.val + 1, by omega⟩ := by
    apply Fin.ext
    dsimp [j]
    omega
  exact eqToHom (congrArg (globalTensorAtlasObject hπ data K (s + 1) hs) hi) ≫
    zeroSplitCyclePositiveIndexedDesc hπ data D s hs hstart hp j F w

/-- Index zero retains the whole infinity chart map. -/
theorem zeroSplitCycleAtlasFamily_infinity :
    zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w 0 =
      zeroSplitCycleInfinityDesc hπ data D s hs hstart (by omega) F := by
  simp only [zeroSplitCycleAtlasFamily, dite_true]

/-- Index one retains the terminal node descent. -/
theorem zeroSplitCycleAtlasFamily_terminal :
    zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w (Fin.succ 0) =
      zeroSplitCycleTerminalDesc hπ data D s hs (by omega) hp F w := by
  simp only [zeroSplitCycleAtlasFamily, Fin.succ_ne_zero, dite_false, dite_true]

/-- The oldest retained chart is the entire start-zero two-node descent. -/
theorem zeroSplitCycleAtlasFamily_zero :
    zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w ⟨s + 2, by omega⟩ =
      zeroSplitCycleZeroIndexedDesc hπ data D s hs hstart hp F w := by
  have h0 : (⟨s + 2, by omega⟩ : Fin (s + 1 + 3)) ≠ 0 := by
    intro h; have H := congrArg Fin.val h; change s + 2 = 0 at H; omega
  have h1 : (⟨s + 2, by omega⟩ : Fin (s + 1 + 3)) ≠ Fin.succ 0 := by
    intro h; have H := congrArg Fin.val h; change s + 2 = 1 at H; omega
  simp only [zeroSplitCycleAtlasFamily, h0, h1, dite_false, dite_true]

/-- The last chart is the original initial chart, with its factorization through infinity. -/
theorem zeroSplitCycleAtlasFamily_initial :
    zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w ⟨s + 3, by omega⟩ =
      zeroSplitCycleInitialDesc hπ data D s hs hstart (by omega) F := by
  have h0 : (⟨s + 3, by omega⟩ : Fin (s + 1 + 3)) ≠ 0 := by
    intro h; have H := congrArg Fin.val h; change s + 3 = 0 at H; omega
  have h1 : (⟨s + 3, by omega⟩ : Fin (s + 1 + 3)) ≠ Fin.succ 0 := by
    intro h; have H := congrArg Fin.val h; change s + 3 = 1 at H; omega
  have h2 : (⟨s + 3, by omega⟩ : Fin (s + 1 + 3)) ≠ ⟨s + 2, by omega⟩ := by
    intro h; have H := congrArg Fin.val h; change s + 3 = s + 2 at H; omega
  simp only [zeroSplitCycleAtlasFamily, h0, h1, h2, dite_false, dite_true]

/-- Positive retained indices preserve the original two-node descents. -/
theorem zeroSplitCycleAtlasFamily_positive (j : Fin s) :
    zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w ⟨s - j.val + 1, by omega⟩ =
      zeroSplitCyclePositiveIndexedDesc hπ data D s hs hstart hp j F w := by
  have h0 : (⟨s - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) ≠ 0 := by
    intro h; have H := congrArg Fin.val h; change s - j.val + 1 = 0 at H; omega
  have h1 : (⟨s - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) ≠ Fin.succ 0 := by
    intro h; have H := congrArg Fin.val h; change s - j.val + 1 = 1 at H; omega
  have h2 : (⟨s - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) ≠ ⟨s + 2, by omega⟩ := by
    intro h; have H := congrArg Fin.val h; change s - j.val + 1 = s + 2 at H; omega
  have h3 : (⟨s - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) ≠ ⟨s + 3, by omega⟩ := by
    intro h; have H := congrArg Fin.val h; change s - j.val + 1 = s + 3 at H; omega
  have hj : s + 1 - (s - j.val + 1) = j.val := by omega
  simp only [zeroSplitCycleAtlasFamily, h0, h1, h2, h3, dite_false]
  have H (k : Fin s) (hk : k = j)
      (he : globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - j.val + 1, by omega⟩ =
        globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - k.val + 1, by omega⟩) :
      eqToHom he ≫ zeroSplitCyclePositiveIndexedDesc hπ data D s hs hstart hp k F w =
        zeroSplitCyclePositiveIndexedDesc hπ data D s hs hstart hp j F w := by
    subst k
    simp only [eqToHom_refl, Category.id_comp]
  exact H _ (Fin.ext hj) _

end FLT.Mazur.WeierstrassDividedDepth
