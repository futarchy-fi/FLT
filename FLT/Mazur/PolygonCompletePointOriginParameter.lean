/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginChart
public import FLT.Mazur.WeierstrassOriginDivisorCoordinates
public import FLT.Mazur.WeierstrassSpecSectionMorphism

/-!
# The original parameter as the pulled normalized X coordinate

The parameter section on the actual localized cubic pulls back to the original
X/Y section ratio. All comparisons retain the genuine structure-sheaf maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "L" => divisorLineBundle (Scheme.Hom.ker (s)) hI
local notation "T" => completePointProjectiveSections K n h i
local notation "U" => sectionGeneratorOpen (tensorPower (L) 3) (T 1)
local notation "V" => completePointOriginOpen K n h i
local notation "g" => completePointToIntegralCubic K n h i

/-- Global-section evaluation of the actual Y-chart map is the original ratio map. -/
theorem completePointToCubicChart_specSectionHom :
    specSectionHom (completePointToCubicChart K n h i 1) =
      completePointIdentityEvaluation K n h i := by
  exact specSectionHom_morphism _

/-- Restricting actual localized coordinates retains the original Y-chart evaluation. -/
theorem completePointToOrigin_coordinate (j : Fin 3) :
    specSectionHom (completePointToOrigin K n h i) (originCoordinate (W) j) =
      (completePointOriginToY K n h i).appTop
        (completePointIdentityEvaluation K n h i (coord (W) 1 j)) := by
  have he := congrArg specSectionHom (completePointToOrigin_chart K n h i)
  change specSectionHom (completePointToOrigin K n h i ≫ Spec.map
    (CommRingCat.ofHom (algebraMap (Coordinate (W) 1) (OriginNeighborhood (W))))) = _ at he
  rw [specSectionHom_comp] at he
  have hc : specSectionHom
      (completePointOriginToY K n h i ≫ completePointToCubicChart K n h i 1) =
        (completePointOriginToY K n h i).appTop.hom.comp
          (completePointIdentityEvaluation K n h i) := by
    rw [← completePointToCubicChart_specSectionHom]
    unfold specSectionHom
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [hc] at he
  exact DFunLike.congr_fun he (coord (W) 1 j)

/-- The pulled original parameter is exactly the original normalized X/Y ratio. -/
theorem completePointToOrigin_parameter :
    (completePointToOrigin K n h i).appTop (originParameterSection (W)) =
      (completePointOriginToY K n h i).appTop
        ((U).topIso.inv
          (sectionRatioOn (tensorPower (L) 3) (T 1) (U) le_rfl (T 0))) := by
  change specSectionHom (completePointToOrigin K n h i) (originCoordinate (W) 0) = _
  rw [completePointToOrigin_coordinate, completePointIdentityEvaluation_coordinate]

end FLT.Mazur.PolygonInfinitesimalStages
