/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalAtlasDesc
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInitialIndexedDesc
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorIndexedDesc
public import FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalIndexedDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalAtlasDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInitialIndexedDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorIndexedDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalIndexedDesc

/-!
# One cyclic family on the original finite global atlas

All five kinds of original chart receive maps from the same compatible family.
The indexing retains the original order, including the distinct original initial chart.
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
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- The chosen cyclic maps form one family on the actual global open cover. -/
def positiveEqualityCycleAtlasFamily (i : Fin (s + 1 + 3)) :
    (globalTensorOpenCover hπ data K (s + 1) hs).X i ⟶ Y := by
  by_cases hzero : i = 0
  · subst i
    exact positiveEqualityCycleInfinityDesc hπ data D s hs hstart (by omega) F
  by_cases hone : i = Fin.succ 0
  · subst i
    exact positiveEqualityCycleTerminalAtlasDesc hπ data D s hs hk hp F
  by_cases hlast : i = ⟨s + 3, by omega⟩
  · subst i
    exact positiveEqualityInitialIndexedDesc hπ data D s hs hstart hk F w
  by_cases htwo : i = ⟨2, by omega⟩
  · subst i
    exact positiveEqualityCycleTerminalIndexedDesc hπ data D s hs hstart hk hp F w
  have hi4 : i.val ≠ 2 := fun h => htwo (Fin.ext h)
  have hi0 : i.val ≠ 0 := fun h => hzero (Fin.ext h)
  have hi1 : i.val ≠ 1 := fun h => hone (Fin.ext h)
  have hi3 : i.val ≠ s + 3 := fun h => hlast (Fin.ext h)
  let j : Fin s := ⟨s + 2 - i.val, by omega⟩
  have hi : i = ⟨s - j.val + 2, by omega⟩ := by
    apply Fin.ext
    dsimp [j]
    omega
  exact eqToHom (congrArg (globalTensorAtlasObject hπ data K (s + 1) hs) hi) ≫
    positiveEqualityCycleInteriorIndexedDesc hπ data D s hs hstart hk j F w

/-- Index zero retains the whole infinity chart map. -/
theorem positiveEqualityCycleAtlasFamily_infinity :
    positiveEqualityCycleAtlasFamily hπ data D s hs hstart hk hp F w 0 =
      positiveEqualityCycleInfinityDesc hπ data D s hs hstart (by omega) F := by
  simp only [positiveEqualityCycleAtlasFamily, dite_true]

/-- Index one retains the terminal Laurent map. -/
theorem positiveEqualityCycleAtlasFamily_terminal :
    positiveEqualityCycleAtlasFamily hπ data D s hs hstart hk hp F w (Fin.succ 0) =
      positiveEqualityCycleTerminalAtlasDesc hπ data D s hs hk hp F := by
  simp only [positiveEqualityCycleAtlasFamily, Fin.succ_ne_zero, dite_false, dite_true]

/-- The last chart is the original initial chart, with its full two-node descent. -/
theorem positiveEqualityCycleAtlasFamily_initial :
    positiveEqualityCycleAtlasFamily hπ data D s hs hstart hk hp F w ⟨s + 3, by omega⟩ =
      positiveEqualityInitialIndexedDesc hπ data D s hs hstart hk F w := by
  have h0 : (⟨s + 3, by omega⟩ : Fin (s + 1 + 3)) ≠ 0 := by
    intro h; have H := congrArg Fin.val h; change s + 3 = 0 at H; omega
  have h1 : (⟨s + 3, by omega⟩ : Fin (s + 1 + 3)) ≠ Fin.succ 0 := by
    intro h; have H := congrArg Fin.val h; change s + 3 = 1 at H; omega
  simp only [positiveEqualityCycleAtlasFamily, h0, h1, dite_false, dite_true]

/-- Index two retains the entire terminal two-node chart with its arbitrary conic constant. -/
theorem positiveEqualityCycleAtlasFamily_terminal_retained :
    positiveEqualityCycleAtlasFamily hπ data D s hs hstart hk hp F w ⟨2, by omega⟩ =
      positiveEqualityCycleTerminalIndexedDesc hπ data D s hs hstart hk hp F w := by
  have h0 : (⟨2, by omega⟩ : Fin (s + 1 + 3)) ≠ 0 := by
    intro h; have H := congrArg Fin.val h; change 2 = 0 at H; omega
  have h1 : (⟨2, by omega⟩ : Fin (s + 1 + 3)) ≠ Fin.succ 0 := by
    intro h; have H := congrArg Fin.val h; change 2 = 1 at H; omega
  have h3 : (⟨2, by omega⟩ : Fin (s + 1 + 3)) ≠ ⟨s + 3, by omega⟩ := by
    intro h; have H := congrArg Fin.val h; change 2 = s + 3 at H; omega
  simp only [positiveEqualityCycleAtlasFamily, h0, h1, h3, dite_false, dite_true]

/-- Positive retained indices preserve the original two-node descents. -/
theorem positiveEqualityCycleAtlasFamily_positive (j : Fin s) :
    positiveEqualityCycleAtlasFamily hπ data D s hs hstart hk hp F w
        ⟨s - j.val + 2, by omega⟩ =
      positiveEqualityCycleInteriorIndexedDesc hπ data D s hs hstart hk j F w := by
  have h0 : (⟨s - j.val + 2, by omega⟩ : Fin (s + 1 + 3)) ≠ 0 := by
    intro h; have H := congrArg Fin.val h; change s - j.val + 2 = 0 at H; omega
  have h1 : (⟨s - j.val + 2, by omega⟩ : Fin (s + 1 + 3)) ≠ Fin.succ 0 := by
    intro h; have H := congrArg Fin.val h; change s - j.val + 2 = 1 at H; omega
  have h3 : (⟨s - j.val + 2, by omega⟩ : Fin (s + 1 + 3)) ≠ ⟨s + 3, by omega⟩ := by
    intro h; have H := congrArg Fin.val h; change s - j.val + 2 = s + 3 at H; omega
  have h4 : (⟨s - j.val + 2, by omega⟩ : Fin (s + 1 + 3)) ≠ ⟨2, by omega⟩ := by
    intro h; have H := congrArg Fin.val h; change s - j.val + 2 = 2 at H; omega
  have hj : s + 2 - (s - j.val + 2) = j.val := by omega
  simp only [positiveEqualityCycleAtlasFamily, h0, h1, h3, h4, dite_false]
  have H (k : Fin s) (heq : k = j)
      (he : globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - j.val + 2, by omega⟩ =
        globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - k.val + 2, by omega⟩) :
      eqToHom he ≫ positiveEqualityCycleInteriorIndexedDesc hπ data D s hs hstart hk k F w =
        positiveEqualityCycleInteriorIndexedDesc hπ data D s hs hstart hk j F w := by
    subst k
    simp only [eqToHom_refl, Category.id_comp]
  exact H _ (Fin.ext hj) _

end FLT.Mazur.WeierstrassDividedDepth
