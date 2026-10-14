/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeTrivializedImages
public import FLT.Mazur.EllipticResolvedTerminalSmoothCharts

/-!
# Exact terminal smooth coverage in the original resolved fiber

At odd depth the arithmetic tori cover precisely the smooth restriction of
the terminal atlas member. At even depth the arithmetic middle torus covers
the entire terminal member. These assertions concern all geometric points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ) (hk0 : 0 < depth / 2)
local notation "F" => ResidueField A
local notation "data" => splitResolutionData A D
local notation "hπ" => SplitNodeDepth.uniformizer_ne_zero D
local notation "p" => resolvedSplitStructure A D
local notation "g" => globalDividedTensorChart hπ data F (depth / 2) (le_refl _)

/-- The arithmetic odd terminal branches cover exactly the terminal smooth restriction. -/
theorem resolvedTerminalCharts_cover (hp : 2 * (depth / 2) < depth) :
    Set.range (resolvedTerminalNegativeChart A D r hk0 hp) ∪
      Set.range (resolvedTerminalPositiveChart A D r hk0 hp) =
        Set.range g ∩ (p).smoothLocus := by
  let c := terminalNodeChart hπ data D (depth / 2) (le_refl _) (by omega) (by omega) (by omega)
  have hs : c ⁻¹' ((p).smoothLocus : Set _) =
      Set.range (PolygonNodeBranches.left F) ∪ Set.range (PolygonNodeBranches.right F) := by
    ext x
    change c x ∈ (p).smoothLocus ↔ _
    rw [PolygonAtlas.mem_smooth_iff c p x]
    have hc : c ≫ p = PolygonNodeBranches.toBase F :=
      terminalNodeChart_structure hπ data D (depth / 2) (le_refl _) _ _ _
    simp only [hc]
    change x ∈ ((PolygonNodePresentation.aToBase F).smoothLocus : Set _) ↔ _
    rw [PolygonNodePresentation.a_smooth_complement,
      ← PolygonNodePresentation.a_zeroLocus_origin,
      ← PolygonNodeBranches.branches_cover_complement]
  change Set.range (nodeTrivializedNegativeChart A hπ data D r _ _ _ _) ∪
    Set.range (nodeTrivializedPositiveChart A hπ data D r _ _ _ _) = _
  rw [nodeTrivializedNegativeChart_range, nodeTrivializedPositiveChart_range]
  change Set.range (_ ≫ c) ∪ Set.range (_ ≫ c) = _
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [← Set.image_union, ← hs, Set.image_preimage_eq_range_inter]
  rw [show Set.range c = Set.range g from
    terminalNodeChart_range hπ data D (depth / 2) (le_refl _) _ _ _]

/-- The odd terminal arithmetic branches have disjoint images in the original fiber. -/
theorem resolvedTerminalCharts_disjoint (hp : 2 * (depth / 2) < depth) :
    Disjoint (Set.range (resolvedTerminalNegativeChart A D r hk0 hp))
      (Set.range (resolvedTerminalPositiveChart A D r hk0 hp)) :=
  nodeTrivializedCharts_disjoint A hπ data D r (depth / 2) (le_refl _) (by omega) (by omega)

/-- At even depth the middle arithmetic torus is the entire terminal geometric chart. -/
theorem resolvedTerminalMiddleChart_range (hm : 2 * (depth / 2) = depth) :
    Set.range (resolvedTerminalMiddleChart A D r hk0 hm) = Set.range g :=
  nodeTrivializedMiddleChart_range A hπ data D r (depth / 2) (le_refl _) (by omega) (by omega)

include r hk0 in
/-- Every point of the even terminal atlas member is smooth over the residue field. -/
theorem resolvedTerminalMiddle_mem_smooth (hm : 2 * (depth / 2) = depth)
    {z : resolvedSplitFiber A D} (hz : z ∈ Set.range g) : z ∈ (p).smoothLocus := by
  rw [← resolvedTerminalMiddleChart_range A D r hk0 hm] at hz
  obtain ⟨x, rfl⟩ := hz
  exact resolvedTerminalMiddleChart_mem_smooth A D r hk0 hm x

/-- The normalized terminal tensor chart is the complete original indexed atlas member. -/
theorem resolvedTerminalTensorChart_range :
    Set.range g =
      Set.range (globalTensorAtlasMap hπ data F (depth / 2) (le_refl _) (Fin.succ 0)) := by
  have he := finiteDividedTensorAtlasIso_map hπ data F (depth / 2) (le_refl _)
  have he := congrArg (fun f => f ≫ finiteLocalTensorEmbedding hπ data F
    (depth / 2) (le_refl _)) he
  rw [Category.assoc] at he
  change _ = g at he
  rw [← he]
  exact SchemeOpenChartRange.range_iso_comp
    (finiteDividedTensorAtlasIso hπ data F (depth / 2) (le_refl _)) _

end FLT.Mazur.WeierstrassDividedDepth
