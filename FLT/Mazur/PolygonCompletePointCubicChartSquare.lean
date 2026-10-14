/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointPointedCubic

/-!
# Cartesian chart squares for the original complete-base cubic map

The normalized coordinate evaluations give actual maps into the affine cubic charts.
Their squares with the original generator opens are Cartesian, without an affineness
assumption on those opens.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "L" => divisorLineBundle (Scheme.Hom.ker (s)) hI
local notation "T" => completePointProjectiveSections K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "U" j => sectionGeneratorOpen (tensorPower (L) 3) (T j)

/-- The original ratio evaluation as a map into the actual affine cubic chart. -/
def completePointToCubicChart (j : Fin 3) :
    (U j).toScheme ⟶ Spec (.of (Coordinate (W) j)) :=
  (U j).toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((U j).topIso.inv.hom.comp
      (sectionCubicChartRingMap (tensorPower (L) 3) (W) (T) j (U j) le_rfl
        (sectionChartScalars (f).appTop.hom (U j))
        (completePointChartCoordinates_equation K n h i j (U j) le_rfl))))

/-- The chart map retains the constructed morphism on the original family. -/
@[reassoc] theorem completePointToCubicChart_inclusion (j : Fin 3) :
    completePointToCubicChart K n h i j ≫ integralCurveChart (W) j =
      (U j).ι ≫ completePointToIntegralCubic K n h i := by
  exact (completePointToIntegralCubic_onChart K n h i j).symm

/-- The original generator-open square is Cartesian, including over the marking. -/
theorem completePointToCubicChart_isPullback (j : Fin 3) :
    IsPullback (completePointToCubicChart K n h i j) (U j).ι
      (integralCurveChart (W) j) (completePointToIntegralCubic K n h i) := by
  apply IsOpenImmersion.isPullback _ _ _ _
    (completePointToCubicChart_inclusion K n h i j).symm
  simpa only [Scheme.Opens.opensRange_ι] using
    completePointToIntegralCubic_preimage_chart K n h i j

/-- The actual chart map is proper, by the retained Cartesian square. -/
theorem completePointToCubicChart_proper (j : Fin 3) :
    IsProper (completePointToCubicChart K n h i j) := by
  let _ := completePointToIntegralCubic_proper K n h i
  exact MorphismProperty.of_isPullback
    (completePointToCubicChart_isPullback K n h i j).flip inferInstance

/-- The chart morphism retains the original complete-base structural map. -/
@[reassoc] theorem completePointToCubicChart_over (j : Fin 3) :
    completePointToCubicChart K n h i j ≫ chartStructure (W) j =
      (U j).ι ≫ (f) ≫ (Spec (.of (PowerSeries K))).toSpecΓ := by
  rw [← integralCurveChart_structure, completePointToCubicChart_inclusion_assoc,
    completePointToIntegralCubic_over]

end FLT.Mazur.PolygonInfinitesimalStages
