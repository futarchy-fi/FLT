/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductDiagramTopology
public import FLT.Mazur.EquifiberedSchemeGluing
public import FLT.Mazur.RelativeGluingMapBase
public import FLT.Mazur.ClosedImmersionCartesianCover

/-!
# The glued subgroup locus inside the full comparison scheme

The concrete closed inclusions form a cartesian natural transformation.
Their colimit is a closed immersion, retaining the original chart inclusions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "X" => normalizedProduct n b c

/-- The concrete closed inclusions form a transformation of the actual affine diagrams. -/
def productSubgroupInclusionDiagram :
    productSubgroupDiagram n b c ⟶ productComparisonDiagram n b c where
  app U := affineSubgroupInclusion n b c (productOpenLeft n b c U) (productOpenRight n b c U)
  naturality {_ _} _ := affineSubgroupOverlapMap_inclusion n b c _ _ _ _ _ _ _

/-- The inclusion transformation retains the entire concrete subgroup pullback square. -/
theorem productSubgroupInclusionDiagram_equifibered :
    (productSubgroupInclusionDiagram n b c).Equifibered := by
  intro U V h
  exact (affineSubgroupOverlap_isPullback n b c _ _ _ _ _
    (productOpenLeft_refine n b c (leOfHom h))
    (productOpenRight_refine n b c (leOfHom h))).flip

/-- The actual subgroup comparison locus in the glued full comparison scheme. -/
def productSubgroupInclusion :
    productSubgroupScheme n b c ⟶ productComparisonScheme n b c :=
  colimMap (productSubgroupInclusionDiagram n b c)

/-- The glued inclusion restricts to the original concrete closed inclusion on every chart. -/
@[reassoc] theorem productSubgroupInclusion_chart (U : (X).affineOpens) :
    (productSubgroupCover n b c).f U ≫ productSubgroupInclusion n b c =
      affineSubgroupInclusion n b c (productOpenLeft n b c U) (productOpenRight n b c U) ≫
        (productComparisonCover n b c).f U :=
  ι_colimMap (productSubgroupInclusionDiagram n b c) U

/-- Every chart of the glued inclusion is the actual original closed subgroup square. -/
theorem productSubgroupInclusion_isPullback (U : (X).affineOpens) :
    IsPullback
      (affineSubgroupInclusion n b c (productOpenLeft n b c U) (productOpenRight n b c U))
      ((productSubgroupCover n b c).f U) ((productComparisonCover n b c).f U)
      (productSubgroupInclusion n b c) := by
  exact Approximation.equifibered_colimit_isPullback
    (productSubgroupInclusionDiagram n b c)
    (productSubgroupInclusionDiagram_equifibered n b c) U

/-- The glued subgroup comparison locus is closed in the full comparison scheme. -/
instance productSubgroupInclusion_closed : IsClosedImmersion (productSubgroupInclusion n b c) :=
  isClosedImmersion_of_cartesian_cover _ (productComparisonCover n b c)
    (productOpenSubgroup n b c) (productSubgroupCover n b c).f
    (fun U ↦ affineSubgroupInclusion n b c (productOpenLeft n b c U) (productOpenRight n b c U))
    (fun U ↦ (productSubgroupInclusion_isPullback n b c U).flip) (fun _ ↦ inferInstance)

/-- The glued closed inclusion retains the same map to the normalized product. -/
@[reassoc] theorem productSubgroupInclusion_structure :
    productSubgroupInclusion n b c ≫ productComparisonStructure n b c =
      productSubgroupStructure n b c :=
  relativeGluing_colimMap_toBase (X).directedAffineCover
    (productSubgroupGluing n b c) (productComparisonGluing n b c)
    (productSubgroupInclusionDiagram n b c) (fun U ↦ by
      change affineSubgroupInclusion n b c _ _ ≫
        (affineComparisonStructure n b c _ _ ≫ U.1.toScheme.isoSpec.inv) =
          affineSubgroupStructure n b c _ _ ≫ U.1.toScheme.isoSpec.inv
      rw [affineSubgroupInclusion_structure_assoc])

end FLT.Mazur.CyclicCharacteristicAtlas
