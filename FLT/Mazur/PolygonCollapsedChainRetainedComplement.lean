/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedChainCartesianAtlas

/-!
# The full chain excludes exactly the retained Laurent open

The equality of full fiber ideals gives the support complement for the actual
closed chain embedding. This excludes the retained edge from chart overlaps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainRetainedComplement
open PolygonCyclicAtlas PolygonCollapsedChainModel PolygonOneGonContraction
open PolygonCollapsedChainOpenCover PolygonCollapsedChainCartesianAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)

/-- The actual chain embedding has the complement of the retained full torus as its range. -/
theorem range_ι : Set.range (chainIdeal K n h i).subschemeι =
    (Set.range (PolygonNodeBranches.left K ≫ chart K n h i))ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι, ← fiberIdeal_eq_chainIdeal,
    fiberIdeal_support, componentι_normalization]
  congr 2
  apply congrArg (fun f : ProjectiveLine.overlap K ⟶ scheme K n h ↦ (f : _ → _))
  change (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫
    componentMap K n h i = PolygonNodeBranches.left K ≫ chart K n h i
  rw [Category.assoc, left_componentMap, overlap_firstBranch_assoc]

/-- No point of the full chain lies on the retained original Laurent edge. -/
theorem retained_edge_ne (x : chain K n h i) (z : ProjectiveLine.overlap K) :
    (chainIdeal K n h i).subschemeι x ≠
      (PolygonNodeBranches.left K ≫ chart K n h i) z := by
  have hx : (chainIdeal K n h i).subschemeι x ∈
      Set.range (chainIdeal K n h i).subschemeι := ⟨x, rfl⟩
  rw [range_ι] at hx
  intro he
  exact hx ⟨z, he.symm⟩

include h in
/-- A left Laurent point visible in any chain chart belongs to an omitted component. -/
theorem left_incidence_omitted (a : ChartIndex n i) (x : chartScheme K n i a)
    (z : ProjectiveLine.overlap K)
    (hz : PolygonNodeBranches.left K z = nodeInclusion K n i a x) :
    nodeIndex n i a ≠ i := by
  intro he
  apply retained_edge_ne K n h i (chartMap K n h i a x) z
  have hx := congrArg (fun f ↦ f x) (chartMap_ι K n h i a)
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← hz, he] at hx
  exact hx

end FLT.Mazur.PolygonCollapsedChainRetainedComplement
