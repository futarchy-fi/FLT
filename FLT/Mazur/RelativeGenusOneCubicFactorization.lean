/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneChartEquation
public import FLT.Mazur.SectionCubicChartMorphism

/-!
# The original family maps to its integral Weierstrass cubic

The normalized chart equations give cubic-valued morphisms on the actual
generator cover. The closed projective embedding detects their agreement,
so they glue to a global factorization over the original base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (Scheme.Modules.pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "L" => divisorLineBundle s.left.ker hI
local notation "T" => relativePointProjectiveSections G hg s hI e
local notation "W" => relativePointWeierstrassCurve G hg s hI e
local notation "C" => sectionGeneratorCover (tensorPower (L) 3) 2 (T)
  (relativePointProjectiveSections_cover G hg s hI e)

/-- The cubic-valued morphism on each original generator open. -/
def relativePointCubicLocal (j : Fin 3) : (C).X j ⟶ integralCurve (W) :=
  sectionCubicChartMorphism (tensorPower (L) 3) (W) (T) j _ le_rfl
    (sectionChartScalars G.hom.appTop.hom _)
    (relativePointChartCoordinates_equation G hg s hI e j _ le_rfl)

/-- Each local cubic morphism retains the original projective map. -/
@[reassoc] theorem relativePointCubicLocal_projective (j : Fin 3) :
    relativePointCubicLocal G hg s hI e j ≫ integralProjectiveMap (W) =
      (C).f j ≫ relativePointToProjectiveSpace G hg s hI e := by
  rw [relativePointCubicLocal, sectionCubicChartMorphism_projectiveMap]
  exact (sectionGeneratorOpen_ι_projectiveMorphism (tensorPower (L) 3) 2 (T)
    (relativePointProjectiveSections_cover G hg s hI e) G.hom.appTop.hom j).symm

/-- The local cubic morphisms agree on the actual categorical overlaps. -/
theorem relativePointCubicLocal_compatible (i j : Fin 3) :
    pullback.fst ((C).f i) ((C).f j) ≫ relativePointCubicLocal G hg s hI e i =
      pullback.snd ((C).f i) ((C).f j) ≫ relativePointCubicLocal G hg s hI e j := by
  apply (cancel_mono (integralProjectiveMap (W))).mp
  simp only [Category.assoc, relativePointCubicLocal_projective]
  rw [← Category.assoc, ← Category.assoc, pullback.condition]

/-- The original family maps globally to its actual integral Weierstrass cubic. -/
def relativePointToIntegralCubic : G.left ⟶ integralCurve (W) :=
  (C).glueMorphisms (relativePointCubicLocal G hg s hI e)
    (relativePointCubicLocal_compatible G hg s hI e)

/-- Gluing retains the concrete local normalized morphisms. -/
@[reassoc] theorem relativePointToIntegralCubic_onChart (j : Fin 3) :
    (C).f j ≫ relativePointToIntegralCubic G hg s hI e =
      relativePointCubicLocal G hg s hI e j :=
  (C).ι_glueMorphisms _ _ j

/-- The global morphism factors the original degree-three projective presentation. -/
@[reassoc] theorem relativePointToIntegralCubic_projective :
    relativePointToIntegralCubic G hg s hI e ≫ integralProjectiveMap (W) =
      relativePointToProjectiveSpace G hg s hI e := by
  apply (C).hom_ext
  intro j
  rw [relativePointToIntegralCubic_onChart_assoc, relativePointCubicLocal_projective]

/-- The factorization preserves the original varying structural morphism. -/
@[reassoc] theorem relativePointToIntegralCubic_over :
    relativePointToIntegralCubic G hg s hI e ≫ integralCurveStructure (W) =
      G.hom ≫ S.toSpecΓ := by
  rw [← integralProjectiveMap_baseProjection,
    relativePointToIntegralCubic_projective_assoc, relativePointToProjectiveSpace_over]

end FLT.Mazur.FCurve
