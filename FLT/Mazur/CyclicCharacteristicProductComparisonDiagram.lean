/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineComparisonCocycle
public import FLT.Mazur.CyclicCharacteristicAffineSubgroupBaseSquare
public import FLT.Mazur.CyclicCharacteristicProductOpenCoordinates

/-!
# The full comparison diagram on the normalized product

Every affine open carries its concrete full Weierstrass comparison scheme.
The proven overlap laws supply a genuine functor, with its original base map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] affineComparisonOverlapMap
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "X" => normalizedProduct n b c
local notation "L" => productOpenLeft n b c
local notation "R" => productOpenRight n b c

/-- The full comparison scheme on each affine open of the normalized product. -/
def productOpenComparison (U : (X).affineOpens) : Scheme :=
  affineComparisonScheme n b c (L U) (R U)

/-- The actual refinement morphism between the full comparison schemes. -/
def productOpenComparisonMap {U V : (X).affineOpens} (h : U ≤ V) :
    productOpenComparison n b c U ⟶ productOpenComparison n b c V :=
  affineComparisonOverlapMap n b c (L V) (R V) (L U) (R U)
    (DirectedAffineSpectrum.restriction X h)
    (productOpenLeft_refine n b c h) (productOpenRight_refine n b c h)

/-- Refining to the same affine open fixes the entire comparison scheme. -/
theorem productOpenComparisonMap_id (U : (X).affineOpens) :
    productOpenComparisonMap n b c (le_refl U) = 𝟙 _ := by
  unfold productOpenComparisonMap
  simp only [DirectedAffineSpectrum.restriction_id]
  apply affineComparisonOverlapMap_id

/-- Refinement composition retains every comparison parameter. -/
theorem productOpenComparisonMap_comp {U V W : (X).affineOpens}
    (h : U ≤ V) (k : V ≤ W) :
    productOpenComparisonMap n b c h ≫ productOpenComparisonMap n b c k =
      productOpenComparisonMap n b c (h.trans k) :=
  affineComparisonOverlapMap_comp n b c (L W) (R W) (L V) (R V) (L U) (R U)
    _ _ _ (DirectedAffineSpectrum.restriction_comp X h k) _ _ _ _ _ _

/-- The full affine comparison schemes form a diagram over all actual affine opens. -/
def productComparisonDiagram : (X).affineOpens ⥤ Scheme where
  obj := productOpenComparison n b c
  map h := productOpenComparisonMap n b c (leOfHom h)
  map_id U := productOpenComparisonMap_id n b c U
  map_comp h k := (productOpenComparisonMap_comp n b c (leOfHom h) (leOfHom k)).symm

/-- The actual base projection into the affine open, in geometric coordinates. -/
def productOpenComparisonStructure (U : (X).affineOpens) :
    productOpenComparison n b c U ⟶ U.1.toScheme :=
  affineComparisonStructure n b c (L U) (R U) ≫ U.1.toScheme.isoSpec.inv

/-- The original coefficient projections commute with geometric open refinement. -/
@[reassoc] theorem productOpenComparisonMap_structure {U V : (X).affineOpens}
    (h : U ≤ V) :
    productOpenComparisonMap n b c h ≫ productOpenComparisonStructure n b c V =
      productOpenComparisonStructure n b c U ≫ (X).homOfLE h := by
  unfold productOpenComparisonMap productOpenComparisonStructure
  rw [affineComparisonOverlapMap_structure_assoc]
  change _ ≫ Spec.map ((X).homOfLE h).appTop ≫ _ = _
  rw [Scheme.isoSpec_inv_naturality, Category.assoc]

/-- The comparison diagram maps naturally to the directed affine cover of the product. -/
def productComparisonProjection :
    productComparisonDiagram n b c ⟶ (X).directedAffineCover.functorOfLocallyDirected where
  app := productOpenComparisonStructure n b c
  naturality {_ _} h := productOpenComparisonMap_structure n b c (leOfHom h)

end FLT.Mazur.CyclicCharacteristicAtlas
