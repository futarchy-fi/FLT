/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneCoordinateSurjective
public import FLT.Mazur.RelativeGenusOneNormalMonomials
public import FLT.Mazur.WeierstrassAffineEvaluationInjective

/-!
# The relative Weierstrass coordinate ring of the original complement

Independent actual monomials make the original evaluation injective, while
pole exhaustion makes it surjective. The ring isomorphism retains the base scalars.
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

local notation "W" => relativePointWeierstrassCurve G hg s hI e

/-- The original relative coordinate evaluation is injective over the actual base ring. -/
theorem relativePointCoordinateEvaluation_injective :
    Function.Injective (relativePointCoordinateEvaluation G hg s hI e) :=
  WeierstrassAffineEquationEvaluation.evaluation_injective (W)
    (relativePointComplementBaseMap G s) (relativePointComplementX G hg s hI e)
    (relativePointComplementY G hg s hI e) (relativePointWeierstrass_equation G hg s hI e)
    (relativePointNormalMonomials_independent G hg s hI e)

/-- The constructed relative cubic ring is the entire original complement function ring. -/
def relativePointCoordinateRingEquiv : (W).toAffine.CoordinateRing ≃+*
    Γ(Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl, ⊤) :=
  RingEquiv.ofBijective (relativePointCoordinateEvaluation G hg s hI e)
    ⟨relativePointCoordinateEvaluation_injective G hg s hI e,
      relativePointCoordinateEvaluation_surjective G hg s hI e⟩

/-- The original base ring map is retained by the constructed ring isomorphism. -/
theorem relativePointCoordinateRingEquiv_scalar (a : Γ(S, ⊤)) :
    relativePointCoordinateRingEquiv G hg s hI e
      (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing a) =
        relativePointComplementBaseMap G s a :=
  relativePointCoordinateEvaluation_scalar G hg s hI e a

/-- The ring isomorphism retains the original order-two function. -/
theorem relativePointCoordinateRingEquiv_x :
    relativePointCoordinateRingEquiv G hg s hI e
      (algebraMap (Polynomial Γ(S, ⊤)) (W).toAffine.CoordinateRing Polynomial.X) =
        relativePointComplementX G hg s hI e :=
  relativePointCoordinateEvaluation_x G hg s hI e

/-- The ring isomorphism retains the original order-three function. -/
theorem relativePointCoordinateRingEquiv_y :
    relativePointCoordinateRingEquiv G hg s hI e (AdjoinRoot.root (W).toAffine.polynomial) =
      relativePointComplementY G hg s hI e :=
  relativePointCoordinateEvaluation_y G hg s hI e

end FLT.Mazur.FCurve
