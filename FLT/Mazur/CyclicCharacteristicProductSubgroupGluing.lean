/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductSubgroupDiagram

/-!
# Gluing the closed subgroup comparison scheme over the normalized product

The concrete affine comparison squares are cartesian. Relative gluing thus
constructs a scheme over the entire product, with the given affine charts
as its actual pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "X" => normalizedProduct n b c

/-- The closed subgroup comparison projection is cartesian on every affine open inclusion. -/
theorem productSubgroupProjection_equifibered :
    (productSubgroupProjection n b c).Equifibered := by
  intro U V h
  exact (DirectedAffineSpectrum.isPullback_toOpen X (leOfHom h) _ _ _
    (affineSubgroupOverlap_base_isPullback n b c
      (productOpenLeft n b c V) (productOpenRight n b c V)
      (productOpenLeft n b c U) (productOpenRight n b c U) _
      (productOpenLeft_refine n b c (leOfHom h))
      (productOpenRight_refine n b c (leOfHom h)))).flip

/-- The proven relative gluing datum of the closed subgroup comparison schemes. -/
def productSubgroupGluing : (X).directedAffineCover.RelativeGluingData where
  functor := productSubgroupDiagram n b c
  natTrans := productSubgroupProjection n b c
  equifibered := productSubgroupProjection_equifibered n b c

/-- The closed subgroup comparison scheme over the entire normalized chart product. -/
def productSubgroupScheme : Scheme := (productSubgroupGluing n b c).glued

/-- Its structure morphism to the actual normalized chart product. -/
def productSubgroupStructure : productSubgroupScheme n b c ⟶ X :=
  (productSubgroupGluing n b c).toBase

/-- The original concrete comparison schemes cover the glued scheme. -/
def productSubgroupCover : (productSubgroupScheme n b c).OpenCover :=
  (productSubgroupGluing n b c).cover

/-- Each original closed subgroup comparison scheme is the actual preimage of its affine open. -/
theorem productSubgroupChart_isPullback (U : (X).affineOpens) :
    IsPullback (productOpenSubgroupStructure n b c U)
      ((productSubgroupCover n b c).f U) U.1.ι (productSubgroupStructure n b c) :=
  (productSubgroupGluing n b c).isPullback_natTrans_ι_toBase U

/-- The glued comparison projection retains the original chart-product base maps. -/
@[reassoc] theorem productSubgroupChart_structure (U : (X).affineOpens) :
    (productSubgroupCover n b c).f U ≫ productSubgroupStructure n b c =
      productOpenSubgroupStructure n b c U ≫ U.1.ι :=
  (productSubgroupGluing n b c).ι_toBase U

end FLT.Mazur.CyclicCharacteristicAtlas
