/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointChartEquation
public import FLT.Mazur.SectionCubicChartMorphism

/-!
# The original complete-base family maps to its integral cubic

The normalized equations glue on the actual generator cover. The resulting
map factors the original projective triple over the original complete base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor relativePoleFunction

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (s)) hI
local notation "T" => completePointProjectiveSections K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "C" => sectionGeneratorCover (tensorPower (L) 3) 2 (T)
  (completePointProjectiveSections_cover K n h i)

/-- The cubic-valued morphism on each original generator open. -/
def completePointCubicLocal (j : Fin 3) : (C).X j ⟶ integralCurve (W) :=
  sectionCubicChartMorphism (tensorPower (L) 3) (W) (T) j _ le_rfl
    (sectionChartScalars (f).appTop.hom _)
    (completePointChartCoordinates_equation K n h i j _ le_rfl)

/-- Each local cubic morphism retains the original projective map. -/
@[reassoc] theorem completePointCubicLocal_projective (j : Fin 3) :
    completePointCubicLocal K n h i j ≫ integralProjectiveMap (W) =
      (C).f j ≫ completePointToProjectiveSpace K n h i := by
  rw [completePointCubicLocal, sectionCubicChartMorphism_projectiveMap]
  exact (sectionGeneratorOpen_ι_projectiveMorphism (tensorPower (L) 3) 2 (T)
    (completePointProjectiveSections_cover K n h i) (f).appTop.hom j).symm

/-- The local cubic morphisms agree on the actual categorical overlaps. -/
theorem completePointCubicLocal_compatible (j k : Fin 3) :
    pullback.fst ((C).f j) ((C).f k) ≫ completePointCubicLocal K n h i j =
      pullback.snd ((C).f j) ((C).f k) ≫ completePointCubicLocal K n h i k := by
  apply (cancel_mono (integralProjectiveMap (W))).mp
  simp only [Category.assoc, completePointCubicLocal_projective]
  rw [← Category.assoc, ← Category.assoc, pullback.condition]

/-- The original family maps globally to its actual integral Weierstrass cubic. -/
def completePointToIntegralCubic : (exactVeroneseProj K n h) ⟶ integralCurve (W) :=
  (C).glueMorphisms (completePointCubicLocal K n h i)
    (completePointCubicLocal_compatible K n h i)

/-- Gluing retains the concrete local normalized morphisms. -/
@[reassoc] theorem completePointToIntegralCubic_onChart (j : Fin 3) :
    (C).f j ≫ completePointToIntegralCubic K n h i =
      completePointCubicLocal K n h i j :=
  (C).ι_glueMorphisms _ _ j

/-- The global morphism factors the original degree-three projective presentation. -/
@[reassoc] theorem completePointToIntegralCubic_projective :
    completePointToIntegralCubic K n h i ≫ integralProjectiveMap (W) =
      completePointToProjectiveSpace K n h i := by
  apply (C).hom_ext
  intro j
  rw [completePointToIntegralCubic_onChart_assoc, completePointCubicLocal_projective]

/-- The factorization preserves the original varying structural morphism. -/
@[reassoc] theorem completePointToIntegralCubic_over :
    completePointToIntegralCubic K n h i ≫ integralCurveStructure (W) =
      f ≫ (Spec (.of (PowerSeries K))).toSpecΓ := by
  rw [← integralProjectiveMap_baseProjection,
    completePointToIntegralCubic_projective_assoc, completePointToProjectiveSpace_over]

end FLT.Mazur.PolygonInfinitesimalStages
