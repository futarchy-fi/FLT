/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicContractionCharts

/-!
# An actual identity-neighborhood comparison with the one-gon contraction

The closed cubic and the explicit contracted one-gon have isomorphic identity
neighborhoods. Both inclusions retain the original maps from the original
closed polygon; the common marking is retained as an actual morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointIdentityCubicOpen

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "D" => closedPointCommonIdentityOpen K n h i
local notation "g" => closedPointToCubic K n h i
local notation "d" => closedPointContraction K n h i
local notation "U" => completePointIdentityBaseChangeOpen K n h (completeClosedBase K) i
local notation "V" => Scheme.Hom.opensRange (Over.Hom.left (PolygonAtlas.torus K 1 0))

/-- Include the common unchanged source into the actual closed cubic. -/
def closedPointCubicIdentityInclusion :
    (D).toScheme ⟶ completePointCubicBaseChange K n h (completeClosedBase K) i := (D).ι ≫ (g)

/-- Include the same common source into the explicitly contracted one-gon. -/
def closedPointOneGonIdentityInclusion : (D).toScheme ⟶ (PolygonAtlas.polygon K 1).left :=
  (D).ι ≫ (d)

instance closedPointCubicIdentityInclusion_open :
    IsOpenImmersion (closedPointCubicIdentityInclusion K n h i) := by
  let _ := closedPointToCubic_identity_isIso K n h i
  exact CommonUnchangedOpenComparison.left_open (g) (d) (U) (V)

instance closedPointOneGonIdentityInclusion_open :
    IsOpenImmersion (closedPointOneGonIdentityInclusion K n h i) := by
  let _ := closedPointContraction_torus_isIso K n h i
  exact CommonUnchangedOpenComparison.right_open (g) (d) (U) (V)

local notation "jC" => closedPointCubicIdentityInclusion K n h i
local notation "jN" => closedPointOneGonIdentityInclusion K n h i

/-- Compare actual target opens through the unchanged original source. -/
def closedPointCubicContractionIdentityIso :
    (jC).opensRange.toScheme ≅ (jN).opensRange.toScheme := by
  let _ := closedPointToCubic_identity_isIso K n h i
  let _ := closedPointContraction_torus_isIso K n h i
  exact CommonUnchangedOpenComparison.targetIso (g) (d) (U) (V)

/-- The forward comparison retains the actual contraction on the common source. -/
@[reassoc] theorem closedPointCubicContractionIdentityIso_hom :
    (jC).isoOpensRange.hom ≫ (closedPointCubicContractionIdentityIso K n h i).hom ≫
      (jN).opensRange.ι = (D).ι ≫ (d) := by
  let _ := closedPointToCubic_identity_isIso K n h i
  let _ := closedPointContraction_torus_isIso K n h i
  exact CommonUnchangedOpenComparison.targetIso_hom_inclusion (g) (d) (U) (V)

/-- The inverse comparison retains the actual cubic map on the common source. -/
@[reassoc] theorem closedPointCubicContractionIdentityIso_inv :
    (jN).isoOpensRange.hom ≫ (closedPointCubicContractionIdentityIso K n h i).inv ≫
      (jC).opensRange.ι = (D).ι ≫ (g) := by
  let _ := closedPointToCubic_identity_isIso K n h i
  let _ := closedPointContraction_torus_isIso K n h i
  exact CommonUnchangedOpenComparison.targetIso_inv_inclusion (g) (d) (U) (V)

/-- The original unit-one marking lifted to the common source. -/
def closedPointCommonIdentityMarking : Spec (.of K) ⟶ (D).toScheme :=
  IsOpenImmersion.lift (D).ι
    (closedPointMarking K n h i)
    (by rw [Scheme.Opens.range_ι]; exact closedPointCommonIdentityOpen_marking_range K n h i)

/-- The common marking preserves the exact original normalization section. -/
@[reassoc] theorem closedPointCommonIdentityMarking_inclusion :
    closedPointCommonIdentityMarking K n h i ≫ (D).ι =
      closedPointMarking K n h i :=
  IsOpenImmersion.lift_fac _ _ _

/-- The common marking maps to the original base-changed cubic zero section. -/
@[reassoc] theorem closedPointCommonIdentityMarking_toCubic :
    closedPointCommonIdentityMarking K n h i ≫ (jC) =
      completePointCubicChangedZero K n h (completeClosedBase K) i := by
  rw [closedPointCubicIdentityInclusion, closedPointCommonIdentityMarking_inclusion_assoc]
  have H := completePointToCubicBaseChange_marking K n h (completeClosedBase K)
    (completeClosedFiberInclusion K n h) (PolygonCyclicAtlas.toBase K n h)
    (completeClosedFiber_isPullback K n h) i
  rw [closedPointMarking_eq_cartesian]
  exact H

/-- The same common marking maps to the original unit-one marking on the contracted one-gon. -/
@[reassoc] theorem closedPointCommonIdentityMarking_toOneGon :
    closedPointCommonIdentityMarking K n h i ≫ (jN) =
      PolygonMarkedSections.sectionMap K 1 (PolygonAtlas.normalization K 1) 1 0 := by
  rw [closedPointOneGonIdentityInclusion, closedPointCommonIdentityMarking_inclusion_assoc,
    closedPointMarking, closedPointContraction, PolygonOneGonContraction.section_contraction]

/-- The comparison identifies the original markings as morphisms, not only as points. -/
@[reassoc] theorem closedPointCubicContractionIdentityIso_marking :
    closedPointCommonIdentityMarking K n h i ≫ (jC).isoOpensRange.hom ≫
      (closedPointCubicContractionIdentityIso K n h i).hom =
        closedPointCommonIdentityMarking K n h i ≫ (jN).isoOpensRange.hom := by
  simp [closedPointCubicContractionIdentityIso, CommonUnchangedOpenComparison.targetIso,
    closedPointCubicIdentityInclusion, closedPointOneGonIdentityInclusion,
    closedPointCommonIdentityOpen]

end FLT.Mazur.PolygonInfinitesimalStages
