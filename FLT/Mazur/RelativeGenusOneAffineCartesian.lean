/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneCubicPreimages
public import FLT.Mazur.RelativeGenusOneAffineRestriction

/-!
# The original affine comparison is the actual cubic-chart pullback

Compose the retained affine isomorphism with the monic-chart comparison.
The exact preimage calculation proves that this square is Cartesian for the
global cubic map over the original varying base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "L" => divisorLineBundle s.left.ker hI
local notation "T" => relativePointProjectiveSections G hg s hI e
local notation "W" => relativePointWeierstrassCurve G hg s hI e
open WeierstrassIntegralChart

local notation "U" => (s.left.ker.support.compl : G.left.Opens)

/-- The original marked-point complement is isomorphic to the integral Z chart. -/
def relativePointIntegralAffineIso :
    (Scheme.Opens.toScheme (X := G.left) (U)) ≅ Spec (.of (Coordinate (W) 2)) :=
  relativePointAffineIso G hg s hI e ≪≫
    Scheme.Spec.mapIso (affineChartMonicEquiv (W)).toRingEquiv.toCommRingCatIso.op

/-- The actual affine isomorphism restricts the global cubic factorization. -/
@[reassoc] theorem relativePointIntegralAffineIso_chart :
    (relativePointIntegralAffineIso G hg s hI e).hom ≫ integralCurveChart (W) 2 =
      (Scheme.Opens.ι (X := G.left) (U)) ≫ relativePointToIntegralCubic G hg s hI e :=
  (relativePointToIntegralCubic_affine G hg s hI e).symm

/-- The retained affine comparison identifies the genuine preimage of the integral Z chart. -/
theorem relativePointIntegralAffine_isPullback :
    IsPullback (relativePointIntegralAffineIso G hg s hI e).hom (Scheme.Opens.ι (X := G.left) (U))
      (integralCurveChart (W) 2) (relativePointToIntegralCubic G hg s hI e) := by
  apply IsOpenImmersion.isPullback
  · exact (relativePointIntegralAffineIso_chart G hg s hI e).symm
  · rw [relativePointToIntegralCubic_preimage_z, Scheme.Opens.opensRange_ι]

/-- On the original marking complement the global cubic map is an open immersion. -/
theorem relativePointToIntegralCubic_affine_isOpenImmersion :
    IsOpenImmersion ((Scheme.Opens.ι (X := G.left) (U)) ≫
      relativePointToIntegralCubic G hg s hI e) := by
  rw [← relativePointIntegralAffineIso_chart]
  infer_instance

end FLT.Mazur.FCurve
