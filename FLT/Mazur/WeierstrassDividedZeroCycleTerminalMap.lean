/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleTerminalExt

/-!
# Descent of a compatible cyclic family on the terminal atlas chart

The first cyclic component is reversed, so its left chart is glued to the
second component's right chart on the actual terminal indexed object.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- The middle cyclic endpoint is the ordered terminal branch compatibility. -/
theorem zeroSplitCycleFamily_terminal_compatible {K : Type u} [Field K]
    (s : ℕ) {Y : Scheme.{u}} (F : Fin (2 * s + 3) → (ProjectiveLine.scheme K ⟶ Y))
    (w : ∀ i, ProjectiveLine.zero K ≫ F i =
      ProjectiveLine.infinity K ≫ F (PolygonPinching.next (by omega) i)) :
    ProjectiveLine.chartZero K ≫ (ProjectiveLine.left K ≫ F ⟨s + 1, by omega⟩) =
      ProjectiveLine.chartZero K ≫ (ProjectiveLine.right K ≫ F ⟨s + 2, by omega⟩) := by
  have hn : PolygonPinching.next (by omega) (⟨s + 1, by omega⟩ : Fin (2 * s + 3)) =
      ⟨s + 2, by omega⟩ := by
    apply Fin.ext
    change (s + 1 + 1) % (2 * s + 3) = s + 2
    exact Nat.mod_eq_of_lt (by omega)
  simpa only [hn, ProjectiveLine.zero, ProjectiveLine.infinity, Category.assoc] using
    w ⟨s + 1, by omega⟩

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "T" => globalTensorAtlasObject hπ data K (s + 1) hs (Fin.succ 0)
local notation "H" => terminalAtlasBranches_isPushout hπ data D s hs hk hp
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- The entire original terminal atlas object carries a descended map from the family. -/
def zeroSplitCycleTerminalDesc : T ⟶ Y :=
  (H).desc _ _ (zeroSplitCycleFamily_terminal_compatible s F w)

/-- The terminal map restricts to the reversed component's left chart. -/
@[reassoc] theorem zeroSplitCycleTerminalDesc_first :
    terminalAtlasFirstBranch hπ data D s hs hk hp ≫
        zeroSplitCycleTerminalDesc hπ data D s hs hk hp F w =
      ProjectiveLine.left K ≫ F ⟨s + 1, by omega⟩ :=
  (H).inl_desc _ _ (zeroSplitCycleFamily_terminal_compatible s F w)

/-- The other terminal restriction is the right chart of the next cyclic component. -/
@[reassoc] theorem zeroSplitCycleTerminalDesc_second :
    terminalAtlasSecondBranch hπ data D s hs hk hp ≫
        zeroSplitCycleTerminalDesc hπ data D s hs hk hp F w =
      ProjectiveLine.right K ≫ F ⟨s + 2, by omega⟩ :=
  (H).inr_desc _ _ (zeroSplitCycleFamily_terminal_compatible s F w)

/-- The two prescribed chart restrictions characterize the terminal map uniquely. -/
theorem zeroSplitCycleTerminalDesc_unique (d : T ⟶ Y)
    (h₁ : terminalAtlasFirstBranch hπ data D s hs hk hp ≫ d =
      ProjectiveLine.left K ≫ F ⟨s + 1, by omega⟩)
    (h₂ : terminalAtlasSecondBranch hπ data D s hs hk hp ≫ d =
      ProjectiveLine.right K ≫ F ⟨s + 2, by omega⟩) :
    d = zeroSplitCycleTerminalDesc hπ data D s hs hk hp F w := by
  apply (H).hom_ext
  · exact h₁.trans (zeroSplitCycleTerminalDesc_first hπ data D s hs hk hp F w).symm
  · exact h₂.trans (zeroSplitCycleTerminalDesc_second hπ data D s hs hk hp F w).symm

end FLT.Mazur.WeierstrassDividedDepth
