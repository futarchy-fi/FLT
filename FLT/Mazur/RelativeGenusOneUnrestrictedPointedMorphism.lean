/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneUnrestrictedPointedCubic

/-!
# The constructed pointed cubic morphism over an arbitrary affine base

The original family maps to its coefficient cubic in the original slice
category, taking the specified marking to the actual infinity section.
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

/-- The constructed coefficient cubic as a scheme over the original base. -/
def relativePointCubicOver : Over S :=
  Over.mk (integralCurveStructure (W) ≫ S.isoSpec.inv)

/-- The infinity marking transported to the original affine base. -/
def relativePointCubicOverZero : 𝟙_ (Over S) ⟶ relativePointCubicOver G hg s hI e :=
  Over.homMk (S.toSpecΓ ≫ integralCurveZero (W)) (by
    change (S.toSpecΓ ≫ integralCurveZero (W)) ≫
      (integralCurveStructure (W) ≫ S.isoSpec.inv) = 𝟙 S
    rw [Category.assoc, ← Category.assoc (integralCurveZero (W)),
      integralCurveZero_structure, Category.id_comp]
    exact S.isoSpec.hom_inv_id)

/-- The original global coordinate morphism is a morphism in the original slice. -/
def relativePointCubicOverMap : G ⟶ relativePointCubicOver G hg s hI e :=
  Over.homMk (relativePointToIntegralCubic G hg s hI e) (by
    change relativePointToIntegralCubic G hg s hI e ≫
      (integralCurveStructure (W) ≫ S.isoSpec.inv) = G.hom
    rw [← Category.assoc, relativePointToIntegralCubic_over, Category.assoc]
    exact Category.comp_id G.hom ▸ congrArg (G.hom ≫ ·) S.isoSpec.hom_inv_id)

/-- The slice morphism sends the actual original marking to infinity. -/
theorem relativePointCubicOverMap_marking :
    s ≫ relativePointCubicOverMap G hg s hI e =
      relativePointCubicOverZero G hg s hI e := by
  apply Over.OverMorphism.ext
  exact relativePointToIntegralCubic_marking G hg s hI e

end FLT.Mazur.FCurve.UnrestrictedPole
