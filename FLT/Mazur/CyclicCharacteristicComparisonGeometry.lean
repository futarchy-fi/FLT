/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductSubgroupInclusion
public import FLT.Mazur.WeierstrassChangeFinitePresentation

/-!
# Geometry of the full comparison scheme over the normalized product

The original equation charts are affine and finitely presented. Their cartesian
squares prove that the full glued comparison map is affine. The closed subgroup
condition therefore gives an affine, locally finite type full relation map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)

/-- Each original equation-comparison chart is affine. -/
instance productOpenComparison_isAffine (V : (normalizedProduct n b c).affineOpens) :
    IsAffine (productOpenComparison n b c V) :=
  inferInstanceAs (IsAffine (Spec _))

/-- The original equation-comparison projection is locally of finite presentation. -/
instance productOpenComparisonStructure_locallyOfFinitePresentation
    (V : (normalizedProduct n b c).affineOpens) :
    LocallyOfFinitePresentation (productOpenComparisonStructure n b c V) := by
  unfold productOpenComparisonStructure affineComparisonStructure
  infer_instance

/-- The full glued comparison projection is affine, by its actual cartesian charts. -/
instance productComparisonStructure_isAffineHom :
    IsAffineHom (productComparisonStructure n b c) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsAffineHom)
    (normalizedProduct n b c).directedAffineCover
  intro V
  let h := (productComparisonChart_isPullback n b c V).flip
  have hi : IsAffineHom (h.isoPullback.inv ≫ productOpenComparisonStructure n b c V) :=
    inferInstance
  rw [h.isoPullback_inv_snd] at hi
  exact hi

/-- Finite presentation of the charts passes to the full comparison morphism. -/
instance productComparisonStructure_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (productComparisonStructure n b c) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation)
    (productComparisonCover n b c)
  intro V
  rw [productComparisonChart_structure]
  infer_instance

/-- The closed subgroup comparison map is affine over the actual normalized product. -/
instance productSubgroupStructure_isAffineHom :
    IsAffineHom (productSubgroupStructure n b c) := by
  rw [← productSubgroupInclusion_structure]
  infer_instance

/-- The full subgroup relation is locally of finite type over the parameter product. -/
instance productSubgroupStructure_locallyOfFiniteType :
    LocallyOfFiniteType (productSubgroupStructure n b c) := by
  rw [← productSubgroupInclusion_structure]
  infer_instance

end FLT.Mazur.CyclicCharacteristicAtlas
