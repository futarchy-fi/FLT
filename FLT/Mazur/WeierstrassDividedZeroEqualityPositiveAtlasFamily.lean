/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityExteriorMaps
public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalAtlasDesc
public import FLT.Mazur.WeierstrassDividedZeroEqualityPositiveInitialDesc
public import FLT.Mazur.WeierstrassDividedZeroEqualityInteriorIndexedDesc
public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalIndexedDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityExteriorMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalAtlasDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveInitialDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorIndexedDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalIndexedDesc

/-!
# One cyclic family on the original finite global atlas

All six kinds of original chart receive maps from the same compatible family.
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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
local notation "K" => ResidueField R
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- The chosen cyclic maps form one family on the actual global open cover. -/
def zeroEqualityPositiveCycleAtlasFamily (i : Fin (s + 1 + 3)) :
    (globalTensorOpenCover hπ data K (s + 1) hs).X i ⟶ Y := by
  by_cases hzero : i = 0
  · subst i
    exact zeroEqualityCycleInfinityDesc hπ data D s hs hstart (by omega) F
  by_cases hone : i = Fin.succ 0
  · subst i
    exact zeroEqualityCycleTerminalAtlasDesc hπ data D s hs hk hp F
  by_cases hold : i = ⟨s + 2, by omega⟩
  · subst i
    exact zeroEqualityPositiveCycleZeroIndexedDesc hπ data D s hs hstart hk hpos F w
  by_cases hlast : i = ⟨s + 3, by omega⟩
  · subst i
    exact zeroEqualityCycleInitialDesc hπ data D s hs hstart (by omega) F
  by_cases htwo : i = ⟨2, by omega⟩
  · subst i
    exact zeroEqualityCycleTerminalIndexedDesc hπ data D s hs hk hp hpos F w
  have hi4 : i.val ≠ 2 := fun h => htwo (Fin.ext h)
  have hi0 : i.val ≠ 0 := fun h => hzero (Fin.ext h)
  have hi1 : i.val ≠ 1 := fun h => hone (Fin.ext h)
  have hi2 : i.val ≠ s + 2 := fun h => hold (Fin.ext h)
  have hi3 : i.val ≠ s + 3 := fun h => hlast (Fin.ext h)
  let j : Fin (s - 1) := ⟨s + 1 - i.val, by omega⟩
  have hi : i = ⟨s - j.val + 1, by omega⟩ := by
    apply Fin.ext
    dsimp [j]
    omega
  exact eqToHom (congrArg (globalTensorAtlasObject hπ data K (s + 1) hs) hi) ≫
    zeroEqualityCycleInteriorIndexedDesc hπ data D s hs hstart hk j F w

/-- Index zero retains the whole infinity chart map. -/
theorem zeroEqualityPositiveCycleAtlasFamily_infinity :
    zeroEqualityPositiveCycleAtlasFamily hπ data D s hs hstart hk hp hpos F w 0 =
      zeroEqualityCycleInfinityDesc hπ data D s hs hstart (by omega) F := by
  simp only [zeroEqualityPositiveCycleAtlasFamily, dite_true]

/-- Index one retains the terminal Laurent map. -/
theorem zeroEqualityPositiveCycleAtlasFamily_terminal :
    zeroEqualityPositiveCycleAtlasFamily hπ data D s hs hstart hk hp hpos F w (Fin.succ 0) =
      zeroEqualityCycleTerminalAtlasDesc hπ data D s hs hk hp F := by
  simp only [zeroEqualityPositiveCycleAtlasFamily, Fin.succ_ne_zero, dite_false, dite_true]

/-- The oldest retained chart is the entire start-zero two-node descent. -/
theorem zeroEqualityPositiveCycleAtlasFamily_zero :
    zeroEqualityPositiveCycleAtlasFamily hπ data D s hs hstart hk hp hpos F w ⟨s + 2, by omega⟩ =
      zeroEqualityPositiveCycleZeroIndexedDesc hπ data D s hs hstart hk hpos F w := by
  have h0 : (⟨s + 2, by omega⟩ : Fin (s + 1 + 3)) ≠ 0 := by
    intro h; have H := congrArg Fin.val h; change s + 2 = 0 at H; omega
  have h1 : (⟨s + 2, by omega⟩ : Fin (s + 1 + 3)) ≠ Fin.succ 0 := by
    intro h; have H := congrArg Fin.val h; change s + 2 = 1 at H; omega
  simp only [zeroEqualityPositiveCycleAtlasFamily, h0, h1, dite_false, dite_true]

/-- The last chart is the original initial chart, with its factorization through infinity. -/
theorem zeroEqualityPositiveCycleAtlasFamily_initial :
    zeroEqualityPositiveCycleAtlasFamily hπ data D s hs hstart hk hp hpos F w ⟨s + 3, by omega⟩ =
      zeroEqualityCycleInitialDesc hπ data D s hs hstart (by omega) F := by
  have h0 : (⟨s + 3, by omega⟩ : Fin (s + 1 + 3)) ≠ 0 := by
    intro h; have H := congrArg Fin.val h; change s + 3 = 0 at H; omega
  have h1 : (⟨s + 3, by omega⟩ : Fin (s + 1 + 3)) ≠ Fin.succ 0 := by
    intro h; have H := congrArg Fin.val h; change s + 3 = 1 at H; omega
  have h2 : (⟨s + 3, by omega⟩ : Fin (s + 1 + 3)) ≠ ⟨s + 2, by omega⟩ := by
    intro h; have H := congrArg Fin.val h; change s + 3 = s + 2 at H; omega
  simp only [zeroEqualityPositiveCycleAtlasFamily, h0, h1, h2, dite_false, dite_true]

/-- Index two retains the entire terminal two-node chart with its arbitrary conic constant. -/
theorem zeroEqualityPositiveCycleAtlasFamily_terminal_retained :
    zeroEqualityPositiveCycleAtlasFamily hπ data D s hs hstart hk hp hpos F w ⟨2, by omega⟩ =
      zeroEqualityCycleTerminalIndexedDesc hπ data D s hs hk hp hpos F w := by
  have h0 : (⟨2, by omega⟩ : Fin (s + 1 + 3)) ≠ 0 := by
    intro h; have H := congrArg Fin.val h; change 2 = 0 at H; omega
  have h1 : (⟨2, by omega⟩ : Fin (s + 1 + 3)) ≠ Fin.succ 0 := by
    intro h; have H := congrArg Fin.val h; change 2 = 1 at H; omega
  have h2 : (⟨2, by omega⟩ : Fin (s + 1 + 3)) ≠ ⟨s + 2, by omega⟩ := by
    intro h; have H := congrArg Fin.val h; change 2 = s + 2 at H; omega
  have h3 : (⟨2, by omega⟩ : Fin (s + 1 + 3)) ≠ ⟨s + 3, by omega⟩ := by
    intro h; have H := congrArg Fin.val h; change 2 = s + 3 at H; omega
  simp only [zeroEqualityPositiveCycleAtlasFamily, h0, h1, h2, h3, dite_false, dite_true]

/-- Positive retained indices preserve the original two-node descents. -/
theorem zeroEqualityPositiveCycleAtlasFamily_positive (j : Fin (s - 1)) :
    zeroEqualityPositiveCycleAtlasFamily hπ data D s hs hstart hk hp hpos F w
        ⟨s - j.val + 1, by omega⟩ =
      zeroEqualityCycleInteriorIndexedDesc hπ data D s hs hstart hk j F w := by
  have h0 : (⟨s - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) ≠ 0 := by
    intro h; have H := congrArg Fin.val h; change s - j.val + 1 = 0 at H; omega
  have h1 : (⟨s - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) ≠ Fin.succ 0 := by
    intro h; have H := congrArg Fin.val h; change s - j.val + 1 = 1 at H; omega
  have h2 : (⟨s - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) ≠ ⟨s + 2, by omega⟩ := by
    intro h; have H := congrArg Fin.val h; change s - j.val + 1 = s + 2 at H; omega
  have h3 : (⟨s - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) ≠ ⟨s + 3, by omega⟩ := by
    intro h; have H := congrArg Fin.val h; change s - j.val + 1 = s + 3 at H; omega
  have h4 : (⟨s - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) ≠ ⟨2, by omega⟩ := by
    intro h; have H := congrArg Fin.val h; change s - j.val + 1 = 2 at H; omega
  have hj : s + 1 - (s - j.val + 1) = j.val := by omega
  simp only [zeroEqualityPositiveCycleAtlasFamily, h0, h1, h2, h3, h4, dite_false]
  have H (k : Fin (s - 1)) (heq : k = j)
      (he : globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - j.val + 1, by omega⟩ =
        globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - k.val + 1, by omega⟩) :
      eqToHom he ≫ zeroEqualityCycleInteriorIndexedDesc hπ data D s hs hstart hk k F w =
        zeroEqualityCycleInteriorIndexedDesc hπ data D s hs hstart hk j F w := by
    subst k
    simp only [eqToHom_refl, Category.id_comp]
  exact H _ (Fin.ext hj) _

end FLT.Mazur.WeierstrassDividedDepth
