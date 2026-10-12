/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneCubicFinite
public import FLT.Mazur.WeierstrassAffineChartDense

/-!
# The relative cubic morphism on underlying spaces

Its image contains the dense affine chart and is closed by properness. The
resulting continuous closed bijection is a homeomorphism. This topological
comparison does not assert that the local rings are already isomorphic.
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

local notation "f" => relativePointToIntegralCubic G hg s hI e

/-- The image contains the entire original affine cubic chart. -/
theorem relativePointToIntegralCubic_range_contains_affine :
    Set.range (integralCurveChart (W) 2) ⊆ Set.range (f) := by
  rintro _ ⟨a, rfl⟩
  let E := relativePointIntegralAffineIso G hg s hI e
  refine ⟨(Scheme.Opens.ι (X := G.left) (U)) (E.inv a), ?_⟩
  have h : E.inv ≫ (Scheme.Opens.ι (X := G.left) (U)) ≫ (f) =
      integralCurveChart (W) 2 := by
    rw [← relativePointIntegralAffineIso_chart, Iso.inv_hom_id_assoc]
  exact congrArg (fun k ↦ k a) h

/-- The original cubic morphism is surjective over arbitrary original bases. -/
theorem relativePointToIntegralCubic_surjective : Function.Surjective (f) := by
  let _ := relativePointToIntegralCubic_proper G hg s hI e
  intro z
  exact closure_minimal (relativePointToIntegralCubic_range_contains_affine G hg s hI e)
    (f).isClosedMap.isClosed_range (integralCurveAffine_denseRange (W) z)

/-- Properness and the affine/marking decomposition give a homeomorphism of underlying spaces. -/
def relativePointIntegralCubicHomeomorph : G.left ≃ₜ integralCurve (W) := by
  let _ := relativePointToIntegralCubic_proper G hg s hI e
  exact (Equiv.ofBijective (f) ⟨relativePointToIntegralCubic_injective G hg s hI e,
    relativePointToIntegralCubic_surjective G hg s hI e⟩).toHomeomorphOfContinuousClosed
      (f).continuous (f).isClosedMap

/-- The homeomorphism retains the actual global cubic morphism on points. -/
theorem relativePointIntegralCubicHomeomorph_apply (x : G.left) :
    relativePointIntegralCubicHomeomorph G hg s hI e x = (f) x := rfl

end FLT.Mazur.FCurve
