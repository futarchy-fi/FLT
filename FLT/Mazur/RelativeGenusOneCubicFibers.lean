/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeComparisonFiberIso
public import FLT.Mazur.RelativeGenusOneCubicFieldIso

/-!
# The scheme fibers of the original cubic morphism

Every field-valued point of the target pulls the original cubic comparison
back to an isomorphism. In particular each scheme-theoretic fiber of that
comparison is its target residue spectrum, including its entire ring structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
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
  (e : (Scheme.Modules.pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅
    structureModule S)

local notation "W" => relativePointWeierstrassCurve G hg s hI e
local notation "f" => relativePointToIntegralCubic G hg s hI e

/-- The actual cubic comparison is an isomorphism above every field-valued target point. -/
theorem relativePointToIntegralCubic_fieldFiber_isIso {K : Type} [Field K]
    (a : Spec (.of K) ⟶ integralCurve (W)) : IsIso (pullback.snd (f) a) := by
  have h := relativePointCubicFieldMap_isIso G hg s hI e (a ≫ integralCurveStructure (W))
  dsimp only [relativePointCubicFieldMap] at h
  let _ := h
  exact relativeComparison_pullback_isIso (G.hom ≫ S.toSpecΓ) (integralCurveStructure (W))
    (f) (relativePointToIntegralCubic_over G hg s hI e) a

/-- The whole scheme fiber of the original global map is the target residue spectrum. -/
theorem relativePointToIntegralCubic_fiber_isIso (y : integralCurve (W)) :
    IsIso ((f).fiberToSpecResidueField y) :=
  relativePointToIntegralCubic_fieldFiber_isIso G hg s hI e
    ((integralCurve (W)).fromSpecResidueField y)

end FLT.Mazur.FCurve
