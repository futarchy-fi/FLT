/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneComplementEquation
public import FLT.Mazur.WeierstrassAffineEquationEvaluation

/-!
# The actual relative morphism to the affine cubic

The constructed equation induces an original coordinate-ring evaluation and
a scheme morphism from the divisor complement, with its base map retained.
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

local notation "x" => relativePointComplementX G hg s hI e
local notation "y" => relativePointComplementY G hg s hI e
local notation "φ" => relativePointComplementBaseMap G s
local notation "W" => relativePointWeierstrassCurve G hg s hI e

/-- Evaluate the constructed affine coordinate ring in the original complement functions. -/
def relativePointCoordinateEvaluation : (W).toAffine.CoordinateRing →+*
    Γ(Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl, ⊤) :=
  WeierstrassAffineEquationEvaluation.evaluation W φ x y
    (relativePointWeierstrass_equation G hg s hI e)

/-- Evaluation retains the original coefficient map. -/
theorem relativePointCoordinateEvaluation_scalar (r : Γ(S, ⊤)) :
    relativePointCoordinateEvaluation G hg s hI e
      (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing r) = φ r :=
  WeierstrassAffineEquationEvaluation.evaluation_scalar W φ x y _ r

/-- The coordinate-ring map is over the actual base ring. -/
theorem relativePointCoordinateEvaluation_comp_scalar :
    (relativePointCoordinateEvaluation G hg s hI e).comp
      (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing) = φ :=
  RingHom.ext (relativePointCoordinateEvaluation_scalar G hg s hI e)

/-- The first universal coordinate evaluates to the original order-two function. -/
theorem relativePointCoordinateEvaluation_x :
    relativePointCoordinateEvaluation G hg s hI e
      (algebraMap (Polynomial Γ(S, ⊤)) (W).toAffine.CoordinateRing Polynomial.X) = x :=
  WeierstrassAffineEquationEvaluation.evaluation_x W φ x y _

/-- The second universal coordinate evaluates to the original order-three function. -/
theorem relativePointCoordinateEvaluation_y :
    relativePointCoordinateEvaluation G hg s hI e (AdjoinRoot.root (W).toAffine.polynomial) = y :=
  WeierstrassAffineEquationEvaluation.evaluation_y W φ x y _

/-- The actual scheme morphism defined by the original normalized pole functions. -/
def relativePointToAffineCubic :
    Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl ⟶
      Spec (.of (W).toAffine.CoordinateRing) :=
  (Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (relativePointCoordinateEvaluation G hg s hI e))

/-- The scheme morphism has the original structure map to the affine base spectrum. -/
theorem relativePointToAffineCubic_over :
    relativePointToAffineCubic G hg s hI e ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing)) =
        (Scheme.Opens.ι (X := G.left) s.left.ker.support.compl) ≫ G.hom ≫ S.toSpecΓ := by
  rw [relativePointToAffineCubic, Category.assoc, ← Spec.map_comp]
  change (Scheme.Opens.toScheme (X := G.left) s.left.ker.support.compl).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom ((relativePointCoordinateEvaluation G hg s hI e).comp
      (algebraMap Γ(S, ⊤) (W).toAffine.CoordinateRing))) = _
  rw [relativePointCoordinateEvaluation_comp_scalar]
  change _ ≫ Spec.map (G.hom.appTop ≫
    (Scheme.Opens.ι (X := G.left) s.left.ker.support.compl).appTop) = _
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← Scheme.toSpecΓ_naturality]

end FLT.Mazur.FCurve
