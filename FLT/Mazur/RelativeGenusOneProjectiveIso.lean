/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFiberClosedImmersion
public import FLT.Mazur.RelativeGenusOneCubicFibers
public import FLT.Mazur.RelativeGenusOneCubicFinite
public import FLT.Mazur.RelativeGenusOnePointedCubic
public import FLT.Mazur.WeierstrassClosedImmersionIso

/-!
# The original relative genus-one curve is its complete pointed cubic

The finite original map has trivial scheme fibers and is a closed immersion.
Its affine chart factors through it; schematic density of the infinity overlap
then eliminates its kernel, even over the original nonreduced coefficient base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open WeierstrassIntegralChart ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "W" => relativePointWeierstrassCurve G hg s hI e
local notation "f" => relativePointToIntegralCubic G hg s hI e

/-- The finite original cubic map is a closed immersion over the entire original base. -/
theorem relativePointToIntegralCubic_isClosedImmersion : IsClosedImmersion (f) := by
  let _ := relativePointToIntegralCubic_finite G hg s hI e
  exact finite_isClosedImmersion_of_isIso_fibers (f)
    (relativePointToIntegralCubic_fiber_isIso G hg s hI e)

/-- The original global cubic factorization is an isomorphism on the full relative curve. -/
theorem relativePointToIntegralCubic_isIso : IsIso (f) := by
  let _ := relativePointToIntegralCubic_isClosedImmersion G hg s hI e
  let E := relativePointIntegralAffineIso G hg s hI e
  apply integralCurve_closedImmersion_isIso_of_affineFactor (W) (f)
    (E.inv ≫ Scheme.Opens.ι (X := G.left) s.left.ker.support.compl)
  dsimp only [E]
  rw [Category.assoc, ← relativePointIntegralAffineIso_chart, Iso.inv_hom_id_assoc]

/-- The complete relative presentation retains the original global coordinate morphism. -/
def relativePointIntegralCubicIso : G.left ≅ integralCurve (W) := by
  let _ := relativePointToIntegralCubic_isIso G hg s hI e
  exact asIso (f)

/-- The full presentation preserves the original varying base map. -/
@[reassoc] theorem relativePointIntegralCubicIso_over :
    (relativePointIntegralCubicIso G hg s hI e).hom ≫ integralCurveStructure (W) =
      G.hom ≫ S.toSpecΓ := relativePointToIntegralCubic_over G hg s hI e

/-- The full presentation preserves the original specified marking. -/
@[reassoc] theorem relativePointIntegralCubicIso_marking :
    s.left ≫ (relativePointIntegralCubicIso G hg s hI e).hom =
      S.toSpecΓ ≫ integralCurveZero (W) := relativePointToIntegralCubic_marking G hg s hI e

/-- In particular the actual local rings at the original marking are isomorphic. -/
theorem relativePointToIntegralCubic_marking_stalkMap_isIso (a : S) :
    IsIso ((f).stalkMap (s.left a)) := by
  let _ := relativePointToIntegralCubic_isIso G hg s hI e
  infer_instance

end FLT.Mazur.FCurve
