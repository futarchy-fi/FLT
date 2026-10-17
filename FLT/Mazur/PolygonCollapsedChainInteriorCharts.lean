/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedChainBoundaryCharts

/-!
# Whole interior node charts of the collapsed chain

An interior node chart factors uniquely through the global closed chain.
Its two branch maps are the original adjacent normalization charts.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainInteriorCharts
open PolygonCyclicAtlas PolygonCollapsedChainModel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i j : Fin n)
  (hj : j ≠ i) (hs : finRotate n j ≠ i)
local notation "I" => chainIdeal K n h i

include hj hs in
/-- The whole original interior node factors through the chain ideal. -/
theorem interior_ker_le : (I).subschemeι.ker ≤ (chart K n h j).ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι,
    ← Scheme.IdealSheafData.map_bot (chart K n h j),
    Scheme.IdealSheafData.le_map_iff_comap_le, ← fiberIdeal_eq_chainIdeal,
    PolygonCollapsedFiberIdeal.interior_chart K n h i j hj hs]

/-- The unchanged original node chart, now as a map into the chain. -/
def interior : PolygonNodeBranches.node K ⟶ chain K n h i :=
  IsClosedImmersion.lift (I).subschemeι (chart K n h j)
    (interior_ker_le K n h i j hj hs)

@[reassoc] theorem interior_ι :
    interior K n h i j hj hs ≫ (I).subschemeι = chart K n h j :=
  IsClosedImmersion.lift_fac _ _ _

/-- The unchanged node is the entire Cartesian restriction of the chain. -/
theorem interior_isPullback : IsPullback (𝟙 (PolygonNodeBranches.node K))
    (interior K n h i j hj hs) (chart K n h j) (I).subschemeι := by
  apply isPullback_of_isClosedImmersion
  · rw [Category.id_comp, interior_ι]
  · rw [Scheme.IdealSheafData.ker_subschemeι, ← fiberIdeal_eq_chainIdeal,
      PolygonCollapsedFiberIdeal.interior_chart K n h i j hj hs,
      Scheme.Hom.ker_eq_bot_of_isIso]

instance interior_isOpenImmersion : IsOpenImmersion (interior K n h i j hj hs) := by
  rw [← (interior_isPullback K n h i j hj hs).isoPullback_hom_snd]
  infer_instance

/-- The first whole branch is the left chart of the original component. -/
@[reassoc] theorem first_interior : firstBranch K ≫ interior K n h i j hj hs =
    ProjectiveLine.left K ≫ component K n h i hj := by
  apply (cancel_mono (I).subschemeι).mp
  rw [Category.assoc, Category.assoc, interior_ι, component_ι, left_componentMap]

/-- The second whole branch is the right chart of the original successor component. -/
@[reassoc] theorem second_interior : secondBranch K ≫ interior K n h i j hj hs =
    ProjectiveLine.right K ≫ component K n h i hs := by
  apply (cancel_mono (I).subschemeι).mp
  rw [Category.assoc, Category.assoc, interior_ι, component_ι, right_componentMap,
    Equiv.symm_apply_apply]

end FLT.Mazur.PolygonCollapsedChainInteriorCharts
