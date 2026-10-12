/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneAffineIso
public import FLT.Mazur.WeierstrassRelativeSmoothDiscriminant
public import FLT.Mazur.WeierstrassIntegralSmooth

/-!
# Nonsingularity of the actual relative genus-one equation

The original complement is smooth. Its affine isomorphism forces the original
coefficient discriminant to be a unit and the full projective cubic to be smooth.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open WeierstrassIntegralChart
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

/-- The equation of the actual original family has unit discriminant over its base ring. -/
theorem relativePointWeierstrass_isElliptic : (W).IsElliptic := by
  let _ := relativePointAffineCubic_smooth G hg s hI e
  exact isElliptic_of_relative_smooth_monic (W)

/-- Nonsingularity is detected in the original ring, without reducing the base. -/
theorem relativePointWeierstrass_discriminant_isUnit : IsUnit (W).Δ := by
  let _ := relativePointWeierstrass_isElliptic G hg s hI e
  exact WeierstrassCurve.isUnit_Δ (W)

/-- The full constructed projective cubic is smooth of relative dimension one. -/
theorem relativePointWeierstrass_projective_smooth_dimension :
    SmoothOfRelativeDimension 1 (integralCurveStructure (W)) :=
  integralCurveStructure_smooth_dimension (W)
    (relativePointWeierstrass_discriminant_isUnit G hg s hI e)

end FLT.Mazur.FCurve
