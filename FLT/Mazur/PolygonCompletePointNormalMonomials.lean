/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointMonomialIndependence
public import FLT.Mazur.RelativeGenusOneNormalMonomials

/-!
# Complete-base monomials in quadratic normal form
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor sectionPoleMultiplicativeCoordinates
  relativePoleFunction completePointAllPoleBasis completePointHigherMonomial

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Spec (CommRingCat.of (PowerSeries K))
local notation "f" => exactVeroneseProjToBase K n h
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "e" => completePointSectionFrame K n h i

/-- Every actual higher section function is the corresponding explicit weighted monomial. -/
theorem completePointHigherMonomial_function (m : ℕ) :
    relativePoleFunction f s hI (m + 2)
      (completePointHigherMonomial K n h i m) =
        WeightedPoleMonomials.monomial (completePointComplementX K n h i)
          (completePointComplementY K n h i) (m + 1) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    rw [completePointHigherMonomial_function_zero]
    simp [WeightedPoleMonomials.monomial, WeightedPoleMonomials.xExponent,
      WeightedPoleMonomials.yExponent]
  | one =>
    rw [completePointHigherMonomial_function_one]
    simp [WeightedPoleMonomials.monomial, WeightedPoleMonomials.xExponent,
      WeightedPoleMonomials.yExponent]
  | more m ih _ =>
    rw [completePointHigherMonomial_function_step, ih, relativePoleWeightedMonomial_step]

/-- The whole independent sequence consists of the actual monomials in x and y. -/
theorem completePointOrderedFunction_monomial (j : ℕ) :
    (show Γ(Scheme.Opens.toScheme (X := exactVeroneseProj K n h) (s).ker.support.compl, ⊤) from
      completePointOrderedFunction K n h i j) =
        WeightedPoleMonomials.monomial (completePointComplementX K n h i)
          (completePointComplementY K n h i) j := by
  cases j with
  | zero =>
    exact (completePointComplement_oneBasis K n h i).trans
      (WeightedPoleMonomials.monomial_zero _ _).symm
  | succ j => exact completePointHigherMonomial_function K n h i j

/-- The original quadratic normal monomials are independent over the actual base ring. -/
theorem completePointNormalMonomials_independent :
    let _ := Module.compHom
      Γ(Scheme.Opens.toScheme (X := exactVeroneseProj K n h) (s).ker.support.compl, ⊤)
      (completePointComplementBaseMap K n h i)
    LinearIndependent Γ(S, ⊤) (fun ab : ℕ × Fin 2 ↦
      completePointComplementX K n h i ^ ab.1 *
        completePointComplementY K n h i ^ ab.2.val) := by
  have hh := (completePointOrderedFunction_independent K n h i).comp
    WeightedPoleMonomials.normalIndex WeightedPoleMonomials.normalIndex_injective
  simpa only [Function.comp_def, completePointOrderedFunction_monomial,
    WeightedPoleMonomials.monomial_normalIndex] using hh


end FLT.Mazur.PolygonInfinitesimalStages
