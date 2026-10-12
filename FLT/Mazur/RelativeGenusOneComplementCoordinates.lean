/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneFramedProducts
public import FLT.Mazur.RelativePoleComplementFunctions

/-!
# Original relative coordinates on the divisor complement

The normalized low-pole lifts give actual regular functions x and y. Their
original tensor products represent the usual powers and mixed product.
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

/-- The base scalars on the actual complement, through its original structure map. -/
def relativePointComplementBaseMap :
    Γ(S, ⊤) →+* Γ(Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl, ⊤) :=
  (Scheme.Opens.ι (X := G.left) s.left.ker.support.compl).appTop.hom.comp G.hom.appTop.hom

/-- The order-two coordinate is the function of the original normalized lift. -/
def relativePointComplementX :
    Γ(Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl, ⊤) :=
  relativePoleFunction G.hom s.left hI 2
    (relativePointFramedLift G hg s hI e 1 (by decide))

/-- The order-three coordinate is the function of the original normalized lift. -/
def relativePointComplementY :
    Γ(Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl, ⊤) :=
  relativePoleFunction G.hom s.left hI 3
    (relativePointFramedLift G hg s hI e 2 (by decide))

/-- The normalized constant has constant function one. -/
theorem relativePointComplement_zeroBasis :
    relativePoleFunction G.hom s.left hI 0 (relativePointZeroBasis G hg s hI ()) = 1 := by
  unfold relativePoleFunction
  exact (congrArg (divisorComplementFunction hI 0)
    (relativePointZeroBasis_section G hg s hI)).trans (divisorComplementFunction_power hI 0)

/-- The canonical degree-one vector still represents the constant one. -/
theorem relativePointComplement_oneBasis :
    relativePoleFunction G.hom s.left hI 1 (relativePointOneBasis G hg s hI ()) = 1 := by
  rw [← relativePoint_initial_step, relativePoleFunction_step,
    relativePointComplement_zeroBasis]

/-- The actual order-four product represents x squared. -/
theorem relativePointComplement_square :
    relativePoleFunction G.hom s.left hI 4 (relativePointFramedSquare G hg s hI e) =
      relativePointComplementX G hg s hI e ^ 2 := by
  exact (relativePoleFunction_product G.hom s.left hI 2 2 _ _).trans
    (pow_two (relativePointComplementX G hg s hI e)).symm

/-- The actual order-five product represents xy. -/
theorem relativePointComplement_mixed :
    relativePoleFunction G.hom s.left hI 5 (relativePointFramedMixed G hg s hI e) =
      relativePointComplementX G hg s hI e * relativePointComplementY G hg s hI e := by
  exact relativePoleFunction_product G.hom s.left hI 2 3 _ _

/-- The original order-six cube represents x cubed. -/
theorem relativePointComplement_cube :
    relativePoleFunction G.hom s.left hI 6 (relativePointFramedCube G hg s hI e) =
      relativePointComplementX G hg s hI e ^ 3 := by
  apply (relativePoleFunction_product G.hom s.left hI 4 2 _ _).trans
  rw [relativePointComplement_square]
  exact (pow_succ (relativePointComplementX G hg s hI e) 2).symm

/-- The original order-six square represents y squared. -/
theorem relativePointComplement_ySquare :
    relativePoleFunction G.hom s.left hI 6 (relativePointFramedYSquare G hg s hI e) =
      relativePointComplementY G hg s hI e ^ 2 := by
  exact (relativePoleFunction_product G.hom s.left hI 3 3 _ _).trans
    (pow_two (relativePointComplementY G hg s hI e)).symm

end FLT.Mazur.FCurve
