/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChartNodeExclusion
public import FLT.Mazur.WeierstrassDividedTerminalNodeChartExclusion
public import FLT.Mazur.WeierstrassDividedFinalRetainedNodesDistinct

/-!
# The terminal node misses all original exterior charts

The entire gluing boundary, rather than only the newest successive chart,
excludes the terminal origin. This separates it from all retained node levels.
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
local notation "d" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "E" => finiteExterior hπ data E₀ (s + 1) hs
local notation "x" => WeierstrassDilatation.x W (π ^ (start + s + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "v" => WeierstrassDilatation.residueNodeIso D (start + (s + 1))
  (by omega) hk (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp
local notation "o" => PolygonNodePresentation.aOrigin K
local notation "f" => finiteStructure hπ data (s + 1) hs
local notation "p" => pullback.snd
  (Spec.map (CommRingCat.ofHom (algebraMap R K))) f
local notation "N" => terminalConicNodeSection hπ data D s hs hk hp

omit [IsBezout R] in
/-- The terminal origin misses the full original exterior after coefficient pullback. -/
theorem terminalTensorNode_exterior_disjoint :
    Disjoint (Set.range ((o ≫ (v).hom) ≫ finiteDividedTensorChart hπ data K (s + 1) hs))
      (p ⁻¹' Set.range (E).exteriorChart) :=
  TensorOpenChart.node_exterior_disjoint f (E).dividedChart (E).exteriorChart
    (finiteDivided_structure hπ data (s + 1) hs) x (E).attach
    (SchemeOpenPushout.isPullback (E).attach (boundaryInclusion d)) (o ≫ (v).hom)
    (terminalNodeTensorOrigin_boundary_disjoint data D s hs hk hp)

/-- Every exterior atlas index, including the initial chart, excludes the terminal node. -/
theorem terminalNode_globalExteriorIndex_disjoint (i : Fin (s + 2)) :
    Disjoint (Set.range N)
      (Set.range (globalTensorAtlasMap hπ data K (s + 1) hs i.succ.succ)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  have hl : finiteTensorAtlasMap hπ data K (s + 1) hs i.succ b =
      ((o ≫ (v).hom) ≫ finiteDividedTensorChart hπ data K (s + 1) hs) a :=
    (finiteLocalTensorEmbedding hπ data K (s + 1) hs).isOpenEmbedding.injective hb
  apply Set.disjoint_left.mp (terminalTensorNode_exterior_disjoint hπ data D s hs hk hp)
    ⟨a, rfl⟩
  rw [← hl]
  have he := congrArg (fun m => m b)
    (finiteTensorAtlasMap_isPullback hπ data K (s + 1) hs i.succ).w
  exact ⟨_, he.symm⟩

/-- The terminal member of the family misses every retained node section. -/
theorem finalNodeSection_terminal_retained_disjoint (j : Fin (s + 1)) (i : Fin 2) :
    Disjoint (Set.range (finalNodeSection hπ data D s hs hk hp (.inr ())))
      (Set.range (finalNodeSection hπ data D s hs hk hp (.inl (.inr (j, i))))) := by
  have H := terminalNode_globalExteriorIndex_disjoint hπ data D s hs hk hp
    ⟨s - j.val, by omega⟩
  apply H.mono_right
  have hr := retainedNodeSectionAt_range hπ data D (s + 1) hs j.val (by omega)
    (by omega) i
  rw [retainedTensorChartAt_range_index] at hr
  have he : (⟨s + 1 - j.val + 1, by omega⟩ : Fin (s + 1 + 3)) =
      (⟨s - j.val, by omega⟩ : Fin (s + 2)).succ.succ := Fin.ext (by dsimp; omega)
  rw [he] at hr
  exact hr

/-- None of the retained ordered nodes is the terminal node. -/
theorem finalNodeSection_terminal_retained_ne (j : Fin (s + 1)) (i : Fin 2) :
    finalNodeSection hπ data D s hs hk hp (.inr ()) ≠
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (j, i))) :=
  nodeMaps_ne_of_disjoint _ _
    (finalNodeSection_terminal_retained_disjoint hπ data D s hs hk hp j i)

end FLT.Mazur.WeierstrassDividedDepth
