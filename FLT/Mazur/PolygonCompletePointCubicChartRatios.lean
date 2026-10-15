/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCubicChartSquare

/-!
# Actual affine cubic coordinates are the retained pole-section ratios

This identifies the section map of the original contraction chart, so its
coordinate equations can be pulled into the complete action relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "L" => completePointLine K n h i
local notation "T" => completePointProjectiveSections K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "U" j => sectionGeneratorOpen (tensorPower (L) 3) (T j)

/-- The full chart section map is the original normalized polynomial evaluation. -/
theorem completePointToCubicChart_functions (j : Fin 3) :
    (Scheme.ΓSpecIso (.of (Coordinate (W) j))).inv ≫
        (completePointToCubicChart K n h i j).appTop =
      CommRingCat.ofHom ((U j).topIso.inv.hom.comp
        (sectionCubicChartRingMap (tensorPower (L) 3) (W) (T) j (U j) le_rfl
          (sectionChartScalars (exactVeroneseProjToBase K n h).appTop.hom (U j))
          (completePointChartCoordinates_equation K n h i j (U j) le_rfl))) := by
  unfold completePointToCubicChart
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Each original affine cubic coordinate is exactly its original pole-section ratio. -/
theorem completePointToCubicChart_coordinate (j k : Fin 3) :
    (completePointToCubicChart K n h i j).appTop
      ((Scheme.ΓSpecIso (.of (Coordinate (W) j))).inv (coord (W) j k)) =
        (U j).topIso.inv (sectionRatioOn (tensorPower (L) 3) (T j) (U j) le_rfl (T k)) := by
  change ((Scheme.ΓSpecIso (.of (Coordinate (W) j))).inv ≫
    (completePointToCubicChart K n h i j).appTop) (coord (W) j k) = _
  rw [completePointToCubicChart_functions]
  exact congrArg (U j).topIso.inv (sectionCubicChartRingMap_coordinate _ _ _ _ _ _ _ _ k)

end FLT.Mazur.PolygonInfinitesimalStages
