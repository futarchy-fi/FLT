/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSubgroupCocycle
public import FLT.Mazur.CyclicCharacteristicAffineSubgroupBaseSquare
public import FLT.Mazur.CyclicCharacteristicProductOpenCoordinates

/-!
# The closed subgroup comparison diagram on the normalized product

Every affine open carries its concrete closed subgroup comparison scheme.
The proven overlap laws supply a genuine functor, with its original base map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] affineSubgroupOverlapMap
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "X" => normalizedProduct n b c
local notation "L" => productOpenLeft n b c
local notation "R" => productOpenRight n b c

/-- The closed subgroup comparison scheme on each affine open of the normalized product. -/
def productOpenSubgroup (U : (X).affineOpens) : Scheme :=
  affineSubgroupScheme n b c (L U) (R U)

/-- The actual refinement morphism between the closed subgroup comparison schemes. -/
def productOpenSubgroupMap {U V : (X).affineOpens} (h : U ≤ V) :
    productOpenSubgroup n b c U ⟶ productOpenSubgroup n b c V :=
  affineSubgroupOverlapMap n b c (L V) (R V) (L U) (R U)
    (DirectedAffineSpectrum.restriction X h)
    (productOpenLeft_refine n b c h) (productOpenRight_refine n b c h)

/-- Refining to the same affine open fixes the entire comparison scheme. -/
theorem productOpenSubgroupMap_id (U : (X).affineOpens) :
    productOpenSubgroupMap n b c (le_refl U) = 𝟙 _ := by
  unfold productOpenSubgroupMap
  simp only [DirectedAffineSpectrum.restriction_id]
  apply affineSubgroupOverlapMap_id

/-- Refinement composition retains every comparison parameter. -/
theorem productOpenSubgroupMap_comp {U V W : (X).affineOpens}
    (h : U ≤ V) (k : V ≤ W) :
    productOpenSubgroupMap n b c h ≫ productOpenSubgroupMap n b c k =
      productOpenSubgroupMap n b c (h.trans k) :=
  affineSubgroupOverlapMap_comp n b c (L W) (R W) (L V) (R V) (L U) (R U)
    _ _ _ (DirectedAffineSpectrum.restriction_comp X h k) _ _ _ _ _ _

/-- The full affine comparison schemes form a diagram over all actual affine opens. -/
def productSubgroupDiagram : (X).affineOpens ⥤ Scheme where
  obj := productOpenSubgroup n b c
  map h := productOpenSubgroupMap n b c (leOfHom h)
  map_id U := productOpenSubgroupMap_id n b c U
  map_comp h k := (productOpenSubgroupMap_comp n b c (leOfHom h) (leOfHom k)).symm

/-- The actual base projection into the affine open, in geometric coordinates. -/
def productOpenSubgroupStructure (U : (X).affineOpens) :
    productOpenSubgroup n b c U ⟶ U.1.toScheme :=
  affineSubgroupStructure n b c (L U) (R U) ≫ U.1.toScheme.isoSpec.inv

/-- The original coefficient projections commute with geometric open refinement. -/
@[reassoc] theorem productOpenSubgroupMap_structure {U V : (X).affineOpens}
    (h : U ≤ V) :
    productOpenSubgroupMap n b c h ≫ productOpenSubgroupStructure n b c V =
      productOpenSubgroupStructure n b c U ≫ (X).homOfLE h := by
  unfold productOpenSubgroupMap productOpenSubgroupStructure
  rw [affineSubgroupOverlapMap_structure_assoc]
  change _ ≫ Spec.map ((X).homOfLE h).appTop ≫ _ = _
  rw [Scheme.isoSpec_inv_naturality, Category.assoc]

/-- The comparison diagram maps naturally to the directed affine cover of the product. -/
def productSubgroupProjection :
    productSubgroupDiagram n b c ⟶ (X).directedAffineCover.functorOfLocallyDirected where
  app := productOpenSubgroupStructure n b c
  naturality {_ _} h := productOpenSubgroupMap_structure n b c (leOfHom h)

end FLT.Mazur.CyclicCharacteristicAtlas
