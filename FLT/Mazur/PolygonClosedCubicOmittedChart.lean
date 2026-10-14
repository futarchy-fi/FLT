/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicContractionCharts
public import FLT.Mazur.PolygonCompletePointCubicPreimages

/-!
# Omitted normalization components lie in the original cubic affine chart

The full original marking ideal pulls back to the unit ideal on each omitted
component. Thus its entire projective line maps into the original Z chart,
with a factorization retaining the exact complete-base cubic morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "c" => completeClosedFiberInclusion K n h

/-- The original complete-base marking pulls back to the unit ideal on omitted components. -/
theorem closedPointOmitted_marking_ideal {j : Fin n} (hj : j ≠ i) :
    (completeBaseMarking K n h i).ker.comap ((componentι K n j ≫ p).left ≫ c) = ⊤ := by
  rw [Scheme.IdealSheafData.comap_comp, completeBaseMarking_ker_closed]
  exact PolygonDivisorNormalizationPullback.other_section_ideal K n (by omega) p
    (PolygonCyclicAtlas.nodes K n h) (PolygonCyclicPushout.isPushout K n h (by omega)) 1 hj

/-- The actual cubic map on one entire original normalization component. -/
def closedPointComponentToOriginalCubic (j : Fin n) :
    ProjectiveLine.scheme K ⟶ integralCurve W :=
  (componentι K n j ≫ p).left ≫ c ≫ g

/-- The original affine cubic chart contains each omitted projective component's full image. -/
theorem closedPointOmitted_preimage_z {j : Fin n} (hj : j ≠ i) :
    closedPointComponentToOriginalCubic K n h i j ⁻¹ᵁ
      (integralCurveChart W 2).opensRange = ⊤ := by
  rw [closedPointComponentToOriginalCubic, Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage, completePointToIntegralCubic_preimage_z]
  have H := congrArg Scheme.IdealSheafData.support
    (closedPointOmitted_marking_ideal K n h i hj)
  rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_top] at H
  ext x
  have hx := congrArg (fun Z ↦ x ∈ Z) H
  change (¬ ((componentι K n j ≫ p).left ≫ c) x ∈
    (completeBaseMarking K n h i).ker.support) ↔ True
  change (((componentι K n j ≫ p).left ≫ c) x ∈
    (completeBaseMarking K n h i).ker.support) = False at hx
  simp only [hx, not_false_eq_true]

/-- The actual component map lifted into the original affine cubic chart. -/
def closedPointOmittedAffineMap {j : Fin n} (hj : j ≠ i) :
    ProjectiveLine.scheme K ⟶ chartScheme W 2 :=
  IsOpenImmersion.lift (integralCurveChart W 2)
    (closedPointComponentToOriginalCubic K n h i j) (by
      rintro _ ⟨x, rfl⟩
      have H := closedPointOmitted_preimage_z K n h i hj
      exact show x ∈ closedPointComponentToOriginalCubic K n h i j ⁻¹ᵁ
        (integralCurveChart W 2).opensRange from H ▸ trivial)

/-- The affine lift retains the original cubic comparison as a scheme morphism. -/
@[reassoc] theorem closedPointOmittedAffineMap_inclusion {j : Fin n} (hj : j ≠ i) :
    closedPointOmittedAffineMap K n h i hj ≫ integralCurveChart W 2 =
      closedPointComponentToOriginalCubic K n h i j :=
  IsOpenImmersion.lift_fac _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
