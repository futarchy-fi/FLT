/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCubicChartSquare
public import FLT.Mazur.WeierstrassOriginNeighborhoodCover

/-!
# The identity parameter equation on the original complete-base chart

The actual Y-chart ratios satisfy zD = x cubed. The denominator restricts to one
on the original marking; these are equations on the original family, without
replacing the generator open by the spectrum of its global sections.
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
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "L" => divisorLineBundle (Scheme.Hom.ker (s)) hI
local notation "T" => completePointProjectiveSections K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "U" => sectionGeneratorOpen (tensorPower (L) 3) (T 1)
local notation "B" => Scheme.Opens.topIso (X := exactVeroneseProj K n h) (U)

/-- Evaluation in the original Y-chart section ring. -/
def completePointIdentityEvaluation : Coordinate (W) 1 →+* Γ((U).toScheme, ⊤) :=
  (B).inv.hom.comp
    (sectionCubicChartRingMap (tensorPower (L) 3) (W) (T) 1 (U) le_rfl
      (sectionChartScalars (f).appTop.hom (U))
      (completePointChartCoordinates_equation K n h i 1 (U) le_rfl))

/-- Coordinate evaluation retains each original normalized ratio. -/
theorem completePointIdentityEvaluation_coordinate (j : Fin 3) :
    completePointIdentityEvaluation K n h i (coord (W) 1 j) =
      (B).inv (sectionRatioOn (tensorPower (L) 3) (T 1) (U) le_rfl (T j)) := by
  unfold completePointIdentityEvaluation
  rw [RingHom.comp_apply, sectionCubicChartRingMap_coordinate]

/-- The original marking evaluates every cubic-chart function at the actual origin. -/
theorem completePointIdentityEvaluation_marking :
    (completePointMarkingY K n h i).appTop.hom.comp
      (completePointIdentityEvaluation K n h i) =
        (chartInfinityEvaluation (S := Γ(S₀, ⊤)) (W)).toRingHom := by
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := projectiveChartAlgebra_surjective (W) 1 a
  have he := DFunLike.congr_fun (completePointMarkingY_chartRingMap K n h i) b
  have hp := DFunLike.congr_fun (sectionCubicChartRingMap_projective
    (tensorPower (L) 3) (W) (T) 1 (U) le_rfl
    (sectionChartScalars (f).appTop.hom (U))
    (completePointChartCoordinates_equation K n h i 1 (U) le_rfl)) b
  exact (congrArg (fun t => (completePointMarkingY K n h i).appTop ((B).inv t)) hp).trans he

/-- The original infinity denominator as a regular function on the original Y open. -/
def completePointIdentityDenominator : Γ((U).toScheme, ⊤) :=
  completePointIdentityEvaluation K n h i (originDenominator (W))

/-- The original ratio coordinates obey the exact parameter equation on the entire Y open. -/
theorem completePointIdentityEquation :
    completePointIdentityEvaluation K n h i (coord (W) 1 2) *
      completePointIdentityDenominator K n h i =
        completePointIdentityEvaluation K n h i (coord (W) 1 0) ^ 3 := by
  simpa only [map_mul, map_pow, completePointIdentityDenominator] using
    congrArg (completePointIdentityEvaluation K n h i) (originDenominator_relation (W))

/-- The parameter denominator is one along the entire original marking. -/
theorem completePointIdentityDenominator_marking :
    (completePointMarkingY K n h i).appTop
      (completePointIdentityDenominator K n h i) = 1 := by
  have he := DFunLike.congr_fun (completePointIdentityEvaluation_marking K n h i)
    (originDenominator (W))
  exact he.trans (originDenominator_at_zero (W))

end FLT.Mazur.PolygonInfinitesimalStages
