/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneComplementCoordinates

/-!
# Unit-leading original monomials in every positive pole order

Starting with the normalized order-two and order-three lifts, multiplication
by the original x section constructs a unit-leading section at every later order.
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

/-- Actual alternating x powers and x powers times y in the original H0 modules. -/
def relativePointHigherMonomial : (m : ℕ) → ModuleRingH G.hom.appTop.hom
    (tensorPower (divisorLineBundle s.left.ker hI) (m + 2)) 0
  | 0 => relativePointFramedLift G hg s hI e 1 (by decide)
  | 1 => relativePointFramedLift G hg s hI e 2 (by decide)
  | m + 2 => sectionPoleHZeroProduct G.hom s.left hI (m + 2) 2
      (relativePointHigherMonomial m) (relativePointFramedLift G hg s hI e 1 (by decide))

/-- The initial higher monomial is the original order-two lift. -/
theorem relativePointHigherMonomial_zero :
    relativePointHigherMonomial G hg s hI e 0 =
      relativePointFramedLift G hg s hI e 1 (by decide) := rfl

/-- The next higher monomial is the original order-three lift. -/
theorem relativePointHigherMonomial_one :
    relativePointHigherMonomial G hg s hI e 1 =
      relativePointFramedLift G hg s hI e 2 (by decide) := rfl

/-- Increasing the order by two uses actual tensor-degree multiplication by x. -/
theorem relativePointHigherMonomial_step (m : ℕ) :
    relativePointHigherMonomial G hg s hI e (m + 2) =
      sectionPoleHZeroProduct G.hom s.left hI (m + 2) 2
        (relativePointHigherMonomial G hg s hI e m)
        (relativePointFramedLift G hg s hI e 1 (by decide)) := rfl

/-- Every constructed monomial has unit leading coefficient in the one original frame. -/
theorem relativePointHigherMonomial_coefficient (m : ℕ) :
    sectionPoleCoefficient s.left hI e (m + 2)
      (moduleH0Equiv _ (relativePointHigherMonomial G hg s hI e m)) = 1 := by
  induction m using Nat.twoStepInduction with
  | zero => exact relativePointFramedLift_coefficient G hg s hI e 1 (by decide)
  | one => exact relativePointFramedLift_coefficient G hg s hI e 2 (by decide)
  | more m ih _ =>
    exact (sectionPoleHZeroProduct_coefficient G.hom s.left hI e (m + 2) 2 _ _).trans
      ((congrArg₂ (fun a b : Γ(S, ⊤) ↦ a * b) ih
        (relativePointFramedLift_coefficient G hg s hI e 1 (by decide))).trans (one_mul 1))

/-- The first function is x itself. -/
theorem relativePointHigherMonomial_function_zero :
    relativePoleFunction G.hom s.left hI 2 (relativePointHigherMonomial G hg s hI e 0) =
      relativePointComplementX G hg s hI e := rfl

/-- The second function is y itself. -/
theorem relativePointHigherMonomial_function_one :
    relativePoleFunction G.hom s.left hI 3 (relativePointHigherMonomial G hg s hI e 1) =
      relativePointComplementY G hg s hI e := rfl

/-- The actual functions satisfy multiplication by x at each two-degree step. -/
theorem relativePointHigherMonomial_function_step (m : ℕ) :
    relativePoleFunction G.hom s.left hI (m + 2 + 2)
      (relativePointHigherMonomial G hg s hI e (m + 2)) =
        relativePoleFunction G.hom s.left hI (m + 2)
          (relativePointHigherMonomial G hg s hI e m) * relativePointComplementX G hg s hI e :=
  relativePoleFunction_product G.hom s.left hI (m + 2) 2 _ _

end FLT.Mazur.FCurve
