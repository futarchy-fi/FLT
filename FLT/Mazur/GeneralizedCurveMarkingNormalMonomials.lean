/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingMonomialIndependence
public import FLT.Mazur.RelativeGenusOneNormalMonomials

/-!
# The higher original functions are exactly the ordered coordinate monomials

Compare the actual section recurrence to the explicit weighted monomial
recurrence. This identifies the independent sequence with the quadratic normal forms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor divisorLineBundle
  sectionPoleMultiplicativeCoordinates Scheme.Modules.pullback
  relativePoleFunction

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

/-- The structure morphism is proper for the original family. -/
local instance generalizedCurveMarkingNormalMonomialsProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- Every actual higher section function is the corresponding explicit weighted monomial. -/
theorem smoothMarkingHigherMonomial_function (m : ℕ) :
    relativePoleFunction E.curve.hom (t).left (hI) (m + 2)
      (smoothMarkingHigherMonomial E s e m) =
        WeightedPoleMonomials.monomial (smoothMarkingComplementX E s e)
          (smoothMarkingComplementY E s e) (m + 1) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    rw [smoothMarkingHigherMonomial_function_zero]
    simp [WeightedPoleMonomials.monomial, WeightedPoleMonomials.xExponent,
      WeightedPoleMonomials.yExponent]
  | one =>
    rw [smoothMarkingHigherMonomial_function_one]
    simp [WeightedPoleMonomials.monomial, WeightedPoleMonomials.xExponent,
      WeightedPoleMonomials.yExponent]
  | more m ih _ =>
    rw [smoothMarkingHigherMonomial_function_step, ih, relativePoleWeightedMonomial_step]

/-- The whole independent sequence consists of the actual monomials in x and y. -/
theorem smoothMarkingOrderedFunction_monomial (j : ℕ) :
    (show Γ(Scheme.Opens.toScheme (X := E.curve.left) (t).left.ker.support.compl, ⊤) from
      smoothMarkingOrderedFunction E s e j) =
        WeightedPoleMonomials.monomial (smoothMarkingComplementX E s e)
          (smoothMarkingComplementY E s e) j := by
  cases j with
  | zero =>
    exact (smoothMarkingComplement_oneBasis E s).trans
      (WeightedPoleMonomials.monomial_zero _ _).symm
  | succ j => exact smoothMarkingHigherMonomial_function E s e j

/-- The original quadratic normal monomials are independent over the actual base ring. -/
theorem smoothMarkingNormalMonomials_independent :
    let _ := Module.compHom
      Γ(Scheme.Opens.toScheme (X := E.curve.left) (t).left.ker.support.compl, ⊤)
      (smoothMarkingComplementBaseMap E s)
    LinearIndependent Γ(S, ⊤) (fun ab : ℕ × Fin 2 ↦
      smoothMarkingComplementX E s e ^ ab.1 *
        smoothMarkingComplementY E s e ^ ab.2.val) := by
  have h := (smoothMarkingOrderedFunction_independent E s e).comp
    WeightedPoleMonomials.normalIndex WeightedPoleMonomials.normalIndex_injective
  simpa only [Function.comp_def, smoothMarkingOrderedFunction_monomial,
    WeightedPoleMonomials.monomial_normalIndex] using h

end FLT.Mazur.GeneralizedEllipticCurve
