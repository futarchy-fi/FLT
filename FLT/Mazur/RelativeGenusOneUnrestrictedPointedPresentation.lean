/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneUnrestrictedProjectiveIso
public import FLT.Mazur.RelativeGenusOneUnrestrictedPointedMorphism

/-!
# The pointed presentation over the original affine base

The complete cubic is viewed over the original scheme through its canonical
affine-spectrum isomorphism. The resulting isomorphism in the original slice
category takes the specified original marking to the actual cubic zero section.

The original base is arbitrary; no Noetherian hypothesis is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve.UnrestrictedPole
open WeierstrassIntegralChart ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme.{0}} [IsAffine S]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "W" => relativePointWeierstrassCurve G hg s hI e

/-- The complete presentation is an isomorphism in the original slice category. -/
def relativePointCubicOverIso : G ≅ relativePointCubicOver G hg s hI e :=
  Over.isoMk (relativePointIntegralCubicIso G hg s hI e) (by
    change (relativePointIntegralCubicIso G hg s hI e).hom ≫
      (integralCurveStructure (W) ≫ S.isoSpec.inv) = G.hom
    rw [← Category.assoc, relativePointIntegralCubicIso_over, Category.assoc]
    exact Category.comp_id G.hom ▸ congrArg (G.hom ≫ ·) S.isoSpec.hom_inv_id)

/-- The full slice isomorphism preserves the specified original marking. -/
theorem relativePointCubicOverIso_marking :
    s ≫ (relativePointCubicOverIso G hg s hI e).hom =
      relativePointCubicOverZero G hg s hI e := by
  apply Over.OverMorphism.ext
  exact relativePointIntegralCubicIso_marking G hg s hI e

end FLT.Mazur.FCurve.UnrestrictedPole
