/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalEdgeCoordinates
public import FLT.Mazur.PolygonInfinitesimalStageFiber
public import FLT.Mazur.PolygonAtlasSmoothLocus

/-!
# Original Laurent components inside every finite polygon stage

The actual normalization torus is the closed fiber of the full Laurent edge
at every finite order. Both inclusions and the coefficient reduction remain
the original morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonInfinitesimal PolygonPinching
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)
local notation "c" => Over.Hom.left
  (torusToComponent K ≫ componentι K n i ≫ PolygonCyclicAtlas.normalization K n h)

/-- The original normalization torus is precisely the specified outgoing closed edge. -/
theorem originalTorus_eq_closedEdge :
    (c) = PolygonNodeBranches.left K ≫ PolygonCyclicAtlas.chart K n h i := by
  rw [PolygonCyclicAtlas.componentι_normalization]
  change (ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K) ≫
    PolygonCyclicAtlas.componentMap K n h i = _
  rw [Category.assoc, PolygonCyclicAtlas.left_componentMap,
    PolygonCyclicAtlas.overlap_firstBranch_assoc]

/-- The original normalization torus agrees with the zero-parameter full edge chart. -/
@[reassoc] theorem originalTorus_zeroFiberIso :
    (c) ≫ (zeroFiberIso K n h).hom = edge K 0 n h i := by
  rw [originalTorus_eq_closedEdge, Category.assoc, chart_zeroFiberIso,
    PolygonSmoothing.specialFiberIso_left_assoc, edge]

/-- The original normalization torus is the actual closed pullback of each full stage edge. -/
theorem originalTorus_stageEdge_isPullback (m : ℕ) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (PolygonScalingNaturality.coeffMap (reduction K m).toRingHom)))
      (c) (edge (Ring K m) (parameter K m) n h i) (specialFiberInclusion K m n h) := by
  apply (edge_parameter_isPullback (parameter K m) n h (reduction K m).toRingHom
    0 (reduction_parameter K m) i).of_iso'
      (Iso.refl _) (Iso.refl _) (zeroFiberIso K n h) (Iso.refl _)
  · simp
  · simpa only [Iso.refl_hom, Category.id_comp] using
      (originalTorus_zeroFiberIso K n h i).symm
  · simp
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl

end FLT.Mazur.PolygonInfinitesimalStages
