/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneMonomialIndependence
public import FLT.Mazur.WeightedPoleNormalForms

/-!
# The higher original functions are exactly the ordered coordinate monomials

Compare the actual section recurrence to the explicit weighted monomial
recurrence. This identifies the independent sequence with the quadratic normal forms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  relativePoleFunction

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

/-- Increasing a positive weighted index by two multiplies its monomial by x. -/
theorem relativePoleWeightedMonomial_step {R : Type*} [CommRing R] (x y : R) (m : ℕ) :
    WeightedPoleMonomials.monomial x y (m + 3) =
      WeightedPoleMonomials.monomial x y (m + 1) * x := by
  have hx : WeightedPoleMonomials.xExponent (m + 3) =
      WeightedPoleMonomials.xExponent (m + 1) + 1 := by
    unfold WeightedPoleMonomials.xExponent
    split_ifs <;> omega
  have hy : WeightedPoleMonomials.yExponent (m + 3) =
      WeightedPoleMonomials.yExponent (m + 1) := by
    have hp : (m + 3 = 0 ∨ (m + 3) % 2 = 1) ↔
        (m + 1 = 0 ∨ (m + 1) % 2 = 1) := by omega
    simp only [WeightedPoleMonomials.yExponent, hp]
  simp only [WeightedPoleMonomials.monomial, hx, hy, pow_succ]
  ac_rfl

/-- Every actual higher section function is the corresponding explicit weighted monomial. -/
theorem relativePointHigherMonomial_function (m : ℕ) :
    relativePoleFunction G.hom s.left hI (m + 2)
      (relativePointHigherMonomial G hg s hI e m) =
        WeightedPoleMonomials.monomial (relativePointComplementX G hg s hI e)
          (relativePointComplementY G hg s hI e) (m + 1) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    rw [relativePointHigherMonomial_function_zero]
    simp [WeightedPoleMonomials.monomial, WeightedPoleMonomials.xExponent,
      WeightedPoleMonomials.yExponent]
  | one =>
    rw [relativePointHigherMonomial_function_one]
    simp [WeightedPoleMonomials.monomial, WeightedPoleMonomials.xExponent,
      WeightedPoleMonomials.yExponent]
  | more m ih _ =>
    rw [relativePointHigherMonomial_function_step, ih, relativePoleWeightedMonomial_step]

/-- The whole independent sequence consists of the actual monomials in x and y. -/
theorem relativePointOrderedFunction_monomial (j : ℕ) :
    (show Γ(Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl, ⊤) from
      relativePointOrderedFunction G hg s hI e j) =
        WeightedPoleMonomials.monomial (relativePointComplementX G hg s hI e)
          (relativePointComplementY G hg s hI e) j := by
  cases j with
  | zero =>
    exact (relativePointComplement_oneBasis G hg s hI).trans
      (WeightedPoleMonomials.monomial_zero _ _).symm
  | succ j => exact relativePointHigherMonomial_function G hg s hI e j

/-- The original quadratic normal monomials are independent over the actual base ring. -/
theorem relativePointNormalMonomials_independent :
    let _ := Module.compHom
      Γ(Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl, ⊤)
      (relativePointComplementBaseMap G s)
    LinearIndependent Γ(S, ⊤) (fun ab : ℕ × Fin 2 ↦
      relativePointComplementX G hg s hI e ^ ab.1 *
        relativePointComplementY G hg s hI e ^ ab.2.val) := by
  have h := (relativePointOrderedFunction_independent G hg s hI e).comp
    WeightedPoleMonomials.normalIndex WeightedPoleMonomials.normalIndex_injective
  simpa only [Function.comp_def, relativePointOrderedFunction_monomial,
    WeightedPoleMonomials.monomial_normalIndex] using h

end FLT.Mazur.FCurve
