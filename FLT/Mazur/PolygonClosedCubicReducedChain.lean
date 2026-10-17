/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicNodeFiber
public import FLT.Mazur.PolygonCollapsedChainModel

/-!
# The actual closed cubic node fiber is the global reduced chain

The original cubic node's pulled ideal equals the reduced union ideal of the
omitted projective components. This constructs an isomorphism of the actual
Cartesian fiber, retaining its inclusion and all original component maps.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonCollapsedChainModel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "f" => closedPointToCubic K n h i
local notation "s" => closedPointCubicNode K n h i

/-- The full original cubic node fiber ideal is the reduced omitted-component union ideal. -/
theorem closedPointToCubic_node_chainIdeal :
    (s).ker.comap (f) = chainIdeal K n h i := by
  rw [closedPointToCubic_node_ideal, fiberIdeal_eq_chainIdeal]

/-- The actual Cartesian closed cubic node fiber is the constructed global reduced chain. -/
def closedPointCubicChainIso : pullback (f) (s) ≅ chain K n h i :=
  asIso (pullback.fst (f) (s)).toImage ≪≫
    BaseAdicThickening.subschemeCongr
      ((Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _).trans
        (closedPointToCubic_node_chainIdeal K n h i))

/-- The comparison retains the original scheme inclusion of the cubic node fiber. -/
@[reassoc] theorem closedPointCubicChainIso_hom_ι :
    (closedPointCubicChainIso K n h i).hom ≫ (chainIdeal K n h i).subschemeι =
      pullback.fst (f) (s) := by
  simp only [closedPointCubicChainIso, Iso.trans_hom, asIso_hom, Category.assoc,
    BaseAdicThickening.subschemeCongr_hom_ι]
  exact Scheme.Hom.toImage_imageι _

/-- The original cubic node fiber itself is reduced, including all its nodes. -/
instance closedPointCubicNodeFiber_isReduced : IsReduced (pullback (f) (s)) :=
  isReduced_of_isOpenImmersion (closedPointCubicChainIso K n h i).hom

/-- Omitted complete components retain their actual scheme maps into the cubic fiber. -/
def closedPointCubicChainComponent {j : Fin n} (hj : j ≠ i) :
    ProjectiveLine.scheme K ⟶ pullback (f) (s) :=
  component K n h i hj ≫ (closedPointCubicChainIso K n h i).inv

/-- Each original component maps into the cubic fiber over its unchanged normalization map. -/
@[reassoc] theorem closedPointCubicChainComponent_fst {j : Fin n} (hj : j ≠ i) :
    closedPointCubicChainComponent K n h i hj ≫ pullback.fst (f) (s) =
      PolygonCyclicAtlas.componentMap K n h j := by
  rw [closedPointCubicChainComponent, Category.assoc,
    ← closedPointCubicChainIso_hom_ι, Iso.inv_hom_id_assoc, component_ι]

end FLT.Mazur.PolygonInfinitesimalStages
