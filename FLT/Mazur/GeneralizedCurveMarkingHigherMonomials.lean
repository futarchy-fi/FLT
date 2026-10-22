/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingComplementCoordinates

/-!
# Unit-leading original monomials in every positive pole order

Starting with the normalized order-two and order-three lifts, multiplication
by the original x section constructs a unit-leading section at every later order.
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
local instance generalizedCurveMarkingHigherMonomialsProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

/-- Actual alternating x powers and x powers times y in the original H0 modules. -/
def smoothMarkingHigherMonomial : (m : ℕ) → ModuleRingH E.curve.hom.appTop.hom
    (tensorPower (divisorLineBundle (t).left.ker (hI)) (m + 2)) 0
  | 0 => smoothMarkingFramedLift E s e 1 (by decide)
  | 1 => smoothMarkingFramedLift E s e 2 (by decide)
  | m + 2 => sectionPoleHZeroProduct E.curve.hom (t).left (hI) (m + 2) 2
      (smoothMarkingHigherMonomial m) (smoothMarkingFramedLift E s e 1 (by decide))

/-- The initial higher monomial is the original order-two lift. -/
theorem smoothMarkingHigherMonomial_zero :
    smoothMarkingHigherMonomial E s e 0 =
      smoothMarkingFramedLift E s e 1 (by decide) := rfl

/-- The next higher monomial is the original order-three lift. -/
theorem smoothMarkingHigherMonomial_one :
    smoothMarkingHigherMonomial E s e 1 =
      smoothMarkingFramedLift E s e 2 (by decide) := rfl

/-- Increasing the order by two uses actual tensor-degree multiplication by x. -/
theorem smoothMarkingHigherMonomial_step (m : ℕ) :
    smoothMarkingHigherMonomial E s e (m + 2) =
      sectionPoleHZeroProduct E.curve.hom (t).left (hI) (m + 2) 2
        (smoothMarkingHigherMonomial E s e m)
        (smoothMarkingFramedLift E s e 1 (by decide)) := rfl

/-- Every constructed monomial has unit leading coefficient in the one original frame. -/
theorem smoothMarkingHigherMonomial_coefficient (m : ℕ) :
    sectionPoleCoefficient (t).left (hI) e (m + 2)
      (moduleH0Equiv _ (smoothMarkingHigherMonomial E s e m)) = 1 := by
  induction m using Nat.twoStepInduction with
  | zero => exact smoothMarkingFramedLift_coefficient E s e 1 (by decide)
  | one => exact smoothMarkingFramedLift_coefficient E s e 2 (by decide)
  | more m ih _ =>
    exact (sectionPoleHZeroProduct_coefficient E.curve.hom (t).left (hI) e (m + 2) 2 _ _).trans
      ((congrArg₂ (fun a b : Γ(S, ⊤) ↦ a * b) ih
        (smoothMarkingFramedLift_coefficient E s e 1 (by decide))).trans (one_mul 1))

/-- The first function is x itself. -/
theorem smoothMarkingHigherMonomial_function_zero :
    relativePoleFunction E.curve.hom (t).left (hI) 2 (smoothMarkingHigherMonomial E s e 0) =
      smoothMarkingComplementX E s e := rfl

/-- The second function is y itself. -/
theorem smoothMarkingHigherMonomial_function_one :
    relativePoleFunction E.curve.hom (t).left (hI) 3 (smoothMarkingHigherMonomial E s e 1) =
      smoothMarkingComplementY E s e := rfl

/-- The actual functions satisfy multiplication by x at each two-degree step. -/
theorem smoothMarkingHigherMonomial_function_step (m : ℕ) :
    relativePoleFunction E.curve.hom (t).left (hI) (m + 2 + 2)
      (smoothMarkingHigherMonomial E s e (m + 2)) =
        relativePoleFunction E.curve.hom (t).left (hI) (m + 2)
          (smoothMarkingHigherMonomial E s e m) * smoothMarkingComplementX E s e :=
  relativePoleFunction_product E.curve.hom (t).left (hI) (m + 2) 2 _ _

end FLT.Mazur.GeneralizedEllipticCurve
