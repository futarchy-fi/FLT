/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicContractionIso
public import FLT.Mazur.PolygonOneGonContractionFiberCharts

/-!
# The exact collapsed fiber of the original closed cubic map

Transport the actual one-gon node through the proved global comparison.
Its full pulled ideal is exactly the contraction fiber ideal, so the omitted
components and the retained endpoint equations keep their scheme structures.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching PolygonOneGonContraction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)
local notation "E" => closedPointContractionCubicIso K n h i

/-- The actual closed-cubic image of the original pinched node, over the original field. -/
def closedPointCubicNode : Spec (.of K) ⟶ (closedPointCubicOver K n h i).left :=
  (targetNode K).left ≫ (E).hom

/-- The transported node retains its closed scheme structure. -/
instance closedPointCubicNode_isClosedImmersion :
    IsClosedImmersion (closedPointCubicNode K n h i) := by
  unfold closedPointCubicNode
  infer_instance

/-- The full node ideal pulls back to the original one-gon node ideal. -/
theorem closedPointCubicNode_ideal :
    (closedPointCubicNode K n h i).ker.comap (E).hom = (targetNode K).left.ker :=
  ProjectiveLineMarkedCharts.ker_comap_mono _ _

/-- The original cubic map has exactly the full contraction fiber, without taking radicals. -/
theorem closedPointToCubic_node_ideal :
    (closedPointCubicNode K n h i).ker.comap (closedPointToCubic K n h i) =
      fiberIdeal K n (by omega) p q hp i := by
  rw [← closedPointContractionCubicIso_fac, Scheme.IdealSheafData.comap_comp,
    closedPointCubicNode_ideal]
  rfl

/-- Every omitted complete component belongs to the cubic node fiber scheme-theoretically. -/
theorem closedPointToCubic_node_ideal_omitted {j : Fin n} (hj : j ≠ i) :
    ((closedPointCubicNode K n h i).ker.comap (closedPointToCubic K n h i)).comap
      (componentι K n j ≫ p).left = ⊥ := by
  rw [closedPointToCubic_node_ideal]
  exact fiberIdeal_omitted K n (by omega) p q hp i hj

/-- The retained affine normalization has the exact two simple endpoint equations. -/
theorem closedPointToCubic_node_ideal_retained_chart :
    ((closedPointCubicNode K n h i).ker.comap (closedPointToCubic K n h i)).comap
      (OneGonAffineNormalization.alpha K ≫ (componentι K n i ≫ p).left) =
        BaseAdicThickening.baseIdeal (.of (Polynomial K))
          (Ideal.span ({Polynomial.X * (Polynomial.X - 1)} : Set (Polynomial K))) := by
  rw [closedPointToCubic_node_ideal]
  exact fiberIdeal_retained_chart K n (by omega) p q hp i

/-- The full retained Laurent chart is disjoint from the cubic node fiber. -/
theorem closedPointToCubic_node_ideal_retained_torus :
    ((closedPointCubicNode K n h i).ker.comap (closedPointToCubic K n h i)).comap
      (torusToComponent K ≫ componentι K n i ≫ p).left = ⊤ := by
  rw [closedPointToCubic_node_ideal]
  exact fiberIdeal_retained_torus K n (by omega) p q hp i

/-- The support is precisely the complement of the original retained Laurent component. -/
theorem closedPointToCubic_node_support :
    (((closedPointCubicNode K n h i).ker.comap (closedPointToCubic K n h i)).support :
      Set (PolygonCyclicAtlas.scheme K n h)) =
        (Set.range (torusToComponent K ≫ componentι K n i ≫ p).left)ᶜ := by
  rw [closedPointToCubic_node_ideal]
  exact fiberIdeal_support K n (by omega) p q hp i

end FLT.Mazur.PolygonInfinitesimalStages
