/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeBranchPushout
public import FLT.Mazur.WeierstrassDividedFinalTerminalComponents

/-!
# The original terminal affine atlas chart is a scheme pushout

The two branches are ordered by the original projective components, so the
first component uses the second node branch. Descent on this chart retains
the original global embedding and works for arbitrary target schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "T" => globalTensorAtlasObject hπ data K (s + 1) hs (Fin.succ 0)
local notation "e" => terminalNodeAtlasIso hπ data D (s + 1) hs (by omega) hk hp
local notation "G" => globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0)

/-- The terminal branch in the first original component, inside the actual atlas object. -/
def terminalAtlasFirstBranch : ProjectiveLine.chart K ⟶ T :=
  PolygonCyclicAtlas.secondBranch K ≫ (e).hom

/-- The other terminal branch, in the second original component's parameterization. -/
def terminalAtlasSecondBranch : ProjectiveLine.chart K ⟶ T :=
  PolygonCyclicAtlas.firstBranch K ≫ (e).hom

omit [IsBezout R] in
/-- The exact indexed terminal chart is the pushout of its original ordered branches. -/
theorem terminalAtlasBranches_isPushout :
    IsPushout (ProjectiveLine.chartZero K) (ProjectiveLine.chartZero K)
      (terminalAtlasFirstBranch hπ data D s hs hk hp)
      (terminalAtlasSecondBranch hπ data D s hs hk hp) :=
  (NodeBranchPushout.isPushout_of_iso K e).flip

/-- The first local branch is exactly the right chart of the original first component. -/
@[reassoc] theorem terminalAtlasFirstBranch_global :
    terminalAtlasFirstBranch hπ data D s hs hk hp ≫ G =
      ProjectiveLine.right K ≫ finalTerminalComponent hπ data D s hs hk hp 0 := by
  rw [terminalAtlasFirstBranch, Category.assoc, terminalNodeAtlasIso_map]
  by_cases h : 0 < start + s
  · rw [finalTerminalComponent_positive hπ data D s hs hk hp h]
    exact (terminalFirstComponent_right hπ data D s hs h hk hp).symm
  · rw [finalTerminalComponent_zero_depth hπ data D s hs hk hp (by omega)]
    exact (terminalZeroFirstComponent_right hπ data D s hs (by omega) hk hp).symm

/-- The second local branch is exactly the right chart of the original second component. -/
@[reassoc] theorem terminalAtlasSecondBranch_global :
    terminalAtlasSecondBranch hπ data D s hs hk hp ≫ G =
      ProjectiveLine.right K ≫ finalTerminalComponent hπ data D s hs hk hp 1 := by
  rw [terminalAtlasSecondBranch, Category.assoc, terminalNodeAtlasIso_map]
  by_cases h : 0 < start + s
  · rw [finalTerminalComponent_positive hπ data D s hs hk hp h]
    exact (terminalSecondComponent_right hπ data D s hs h hk hp).symm
  · rw [finalTerminalComponent_zero_depth hπ data D s hs hk hp (by omega)]
    exact (terminalZeroSecondComponent_right hπ data D s hs (by omega) hk hp).symm

omit [IsBezout R] in
/-- Compatible complete component maps descend uniquely on the actual terminal affine chart. -/
theorem terminalAtlas_exists_unique_desc {Y : Scheme.{u}}
    (f g : ProjectiveLine.scheme K ⟶ Y)
    (w : ProjectiveLine.infinity K ≫ f = ProjectiveLine.infinity K ≫ g) :
    ∃! d : T ⟶ Y,
      terminalAtlasFirstBranch hπ data D s hs hk hp ≫ d = ProjectiveLine.right K ≫ f ∧
      terminalAtlasSecondBranch hπ data D s hs hk hp ≫ d = ProjectiveLine.right K ≫ g := by
  have w' : ProjectiveLine.chartZero K ≫ (ProjectiveLine.right K ≫ f) =
      ProjectiveLine.chartZero K ≫ (ProjectiveLine.right K ≫ g) := by
    simpa only [ProjectiveLine.infinity, Category.assoc] using w
  let H := terminalAtlasBranches_isPushout hπ data D s hs hk hp
  refine ⟨H.desc _ _ w', ⟨H.inl_desc _ _ w', H.inr_desc _ _ w'⟩, ?_⟩
  intro d hd
  apply H.hom_ext
  · exact hd.1.trans (H.inl_desc _ _ w').symm
  · exact hd.2.trans (H.inr_desc _ _ w').symm

end FLT.Mazur.WeierstrassDividedDepth
