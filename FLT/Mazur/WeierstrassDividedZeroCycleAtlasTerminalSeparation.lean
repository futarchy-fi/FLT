/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonCyclicNormalizationFinite
public import FLT.Mazur.WeierstrassDividedExteriorTerminalExclusions
public import FLT.Mazur.WeierstrassDividedZeroCycleTerminalMap

/-!
# The entire terminal atlas chart misses infinity

The two original affine branches cover the full terminal chart. Their images
lie in the actual complete terminal components, which are disjoint from infinity.
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
local notation "e" => terminalNodeAtlasIso hπ data D (s + 1) hs (by omega) hk hp
local notation "T" => globalTensorAtlasObject hπ data K (s + 1) hs (Fin.succ 0)
local notation "G" => globalTensorAtlasMap hπ data K (s + 1) hs (Fin.succ 0)

omit [IsBezout R] in
/-- The original two ordered branches cover every point of the entire terminal chart. -/
theorem terminalAtlasBranches_cover (z : T) :
    (∃ a, terminalAtlasFirstBranch hπ data D s hs hk hp a = z) ∨
      (∃ b, terminalAtlasSecondBranch hπ data D s hs hk hp b = z) := by
  obtain ⟨a, ha⟩ := PolygonCyclicNormalizationFinite.affine_surjective K ((e).inv z)
  obtain ⟨a | a, rfl⟩ := (coprodMk _ _).surjective a
  · right
    refine ⟨a, ?_⟩
    have H := congrArg (fun x => (e).hom x) ha
    rw [coprodMk_inl] at H
    change (coprod.inl ≫ PolygonCyclicNormalizationPullback.affineNormalization K ≫
      (e).hom) a = _ at H
    simp only [PolygonCyclicNormalizationPullback.affineNormalization,
      coprod.inl_desc_assoc, ← Scheme.Hom.comp_apply, Iso.inv_hom_id] at H
    exact H
  · left
    refine ⟨a, ?_⟩
    have H := congrArg (fun x => (e).hom x) ha
    rw [coprodMk_inr] at H
    change (coprod.inr ≫ PolygonCyclicNormalizationPullback.affineNormalization K ≫
      (e).hom) a = _ at H
    simp only [PolygonCyclicNormalizationPullback.affineNormalization,
      coprod.inr_desc_assoc, ← Scheme.Hom.comp_apply, Iso.inv_hom_id] at H
    exact H

include D hk hp in
/-- The full terminal atlas object, including its origin, has no infinity intersection. -/
theorem zeroSplitCycleAtlas_terminal_infinity_disjoint :
    Disjoint (Set.range G)
      (Set.range (globalTensorAtlasMap hπ data K (s + 1) hs 0)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, rfl⟩ hz
  rcases terminalAtlasBranches_cover hπ data D s hs hk hp z with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · have he := congrArg (fun f => f a)
      (terminalAtlasFirstBranch_global hπ data D s hs hk hp)
    exact Set.disjoint_left.mp
      (finalTerminalComponent_infinity_chart_disjoint hπ data D s hs hk hp 0)
      ⟨ProjectiveLine.right K a, he.symm⟩ hz
  · have he := congrArg (fun f => f a)
      (terminalAtlasSecondBranch_global hπ data D s hs hk hp)
    exact Set.disjoint_left.mp
      (finalTerminalComponent_infinity_chart_disjoint hπ data D s hs hk hp 1)
      ⟨ProjectiveLine.right K a, he.symm⟩ hz

include D hk hp in
/-- The actual terminal/infinity fiber product is the empty scheme. -/
theorem zeroSplitCycleAtlas_terminal_infinity_isEmpty :
    IsEmpty (Limits.pullback G
      (globalTensorAtlasMap hπ data K (s + 1) hs 0) : Scheme) :=
  Scheme.isEmpty_pullback _ _
    (zeroSplitCycleAtlas_terminal_infinity_disjoint hπ data D s hs hk hp)

end FLT.Mazur.WeierstrassDividedDepth
