/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointHomogeneousEquation
public import FLT.Mazur.SectionCubicRatioNormalization
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

/-!
# The integral cubic equation on every original generator chart

Dividing the actual homogeneous relation by a generator cube gives its
normalized equation on each chart, including the chart through the marking.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor relativePoleFunction
  SectionGradedMultiplication.mul degreeThreeCubicProduct completePointCubicProduct

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (s)) hI
local notation "T" => completePointProjectiveSections K n h i
local notation "W" => completePointWeierstrassCurve K n h i

/-- The regular normalized coordinates on a subopen of an original generator chart. -/
def completePointChartCoordinates (j : Fin 3) (U : (exactVeroneseProj K n h).Opens)
    (hj : U ≤ sectionGeneratorOpen (tensorPower (L) 3) (T j)) :
    Fin 3 → Γ((exactVeroneseProj K n h), U) :=
  fun i => sectionRatioOn (tensorPower (L) 3) (T j) U hj (T i)

/-- The selected coordinate is exactly one. -/
theorem completePointChartCoordinates_self (j : Fin 3) (U : (exactVeroneseProj K n h).Opens)
    (hj : U ≤ sectionGeneratorOpen (tensorPower (L) 3) (T j)) :
    completePointChartCoordinates K n h i j U hj j = 1 :=
  sectionRatioOn_self _ _ _ _

/-- Every actual generator chart satisfies the normalized original cubic equation. -/
theorem completePointChartCoordinates_equation (j : Fin 3) (U : (exactVeroneseProj K n h).Opens)
    (hj : U ≤ sectionGeneratorOpen (tensorPower (L) 3) (T j)) :
    ((W).map (sectionChartScalars (f).appTop.hom U)).toProjective.Equation
      (completePointChartCoordinates K n h i j U hj) := by
  rw [WeierstrassCurve.Projective.equation_iff, sub_eq_zero]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    pow_succ, pow_zero, one_mul]
  apply degreeThreeCubicProduct_smul_injective (L) (hI).divisorLineBundle_locallyFreeRankOne
    (T j) U hj
  have he := congrArg ((tensorPower (L) 9).presheaf.map U.leTop.op)
    (completePointProjectiveSections_equation K n h i)
  simp only [map_add, (tensorPower (L) 9).map_smul] at he
  have hp (a b c : Γ(tensorPower (L) 3, ⊤)) :
      (tensorPower (L) 9).presheaf.map U.leTop.op
        (completePointCubicProduct K n h i a b c) =
      (sectionRatioOn (tensorPower (L) 3) (T j) U hj a *
        sectionRatioOn (tensorPower (L) 3) (T j) U hj b *
        sectionRatioOn (tensorPower (L) 3) (T j) U hj c) •
      (tensorPower (L) 9).presheaf.map U.leTop.op
        (degreeThreeCubicProduct (L) ⊤ (T j) (T j) (T j)) :=
    by simpa only [completePointCubicProduct, degreeThreeCubicProduct] using
      (degreeThreeCubicProduct_ratios (L) (T j) a b c U hj).symm
  simp only [hp, smul_smul, ← add_smul] at he
  simp only [completePointChartCoordinates, completePointProjectiveSections,
    sectionChartScalars, RingHom.comp_apply, WeierstrassCurve.Projective.fin3_def_ext,
    mul_assoc] at he ⊢
  convert he using 1 <;> rfl

end FLT.Mazur.PolygonInfinitesimalStages
