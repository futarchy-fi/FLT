/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCubicChartSquare
public import FLT.Mazur.PolygonCompletePointCubicChartAffinization
public import FLT.Mazur.AffineProperFunctionSheaf

/-!
# Relative functions on the original cubic Z chart

The actual complement map is proper and its direct-image structure sheaf is
the original chart structure sheaf. This retains every restriction of functions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "s" => completeBaseMarking K n h i
local notation "U" => GlobalIdealPowerCompatibility.complement (Scheme.Hom.ker (s))
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "c" => completePointComplementToCubicChart K n h i

/-- The original complement chart square is Cartesian on the entire complete family. -/
theorem completePointComplementToCubicChart_isPullback :
    IsPullback (c) (U).ι (integralCurveChart (W) 2) (g) := by
  apply IsOpenImmersion.isPullback _ _ _ _
    (completePointComplementToCubicChart_inclusion K n h i).symm
  rw [Scheme.Opens.opensRange_ι, completePointToIntegralCubic_preimage_z]

/-- The complement affinization is the proper restriction of the original contraction. -/
theorem completePointComplementToCubicChart_proper : IsProper (c) := by
  let _ := completePointToIntegralCubic_proper K n h i
  exact MorphismProperty.of_isPullback
    (completePointComplementToCubicChart_isPullback K n h i).flip inferInstance

/-- Global functions are pulled back by the actual chart morphism isomorphically. -/
theorem completePointComplementToCubicChart_appTop_isIso : IsIso (c).appTop := by
  change IsIso (((U).toScheme.toSpecΓ ≫
    (completePointComplementSpectrumIso K n h i).hom ≫
      (completePointMonicChartIso K n h i).hom).appTop)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  infer_instance

/-- Every chart open has exactly the functions of its actual inverse image. -/
theorem completePointComplementToCubicChart_app_isIso
    (V : (Spec (.of (Coordinate (W) 2))).Opens) : IsIso ((c).app V) := by
  let _ := completePointComplementToCubicChart_proper K n h i
  let _ := completePointComplementToCubicChart_appTop_isIso K n h i
  exact AffineProperFunctionSheaf.app_isIso (c)
    (ConcreteCategory.bijective_of_isIso (c).appTop) V

/-- The relative ring-sheaf identification on the actual cubic Z chart. -/
def completePointCubicChartStructureSheafIso :
    (Spec (.of (Coordinate (W) 2))).sheaf ≅
      (TopCat.Sheaf.pushforward CommRingCat (c).base).obj (U).toScheme.sheaf := by
  let _ := completePointComplementToCubicChart_proper K n h i
  let _ := completePointComplementToCubicChart_appTop_isIso K n h i
  let _ := AffineProperFunctionSheaf.structureMap_isIso (c)
    (ConcreteCategory.bijective_of_isIso (c).appTop)
  exact asIso (ArtinianProperStructureSheaf.structureMap (q := c))

/-- The sheaf identification preserves the original map on every open, not just constants. -/
theorem completePointCubicChartStructureSheafIso_app
    (V : (Spec (.of (Coordinate (W) 2))).Opens) :
    (completePointCubicChartStructureSheafIso K n h i).hom.hom.app (.op V) = (c).app V :=
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
