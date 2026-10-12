/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneMarkedCoordinates
public import FLT.Mazur.SectionPoleCanonicalCoefficient
public import FLT.Mazur.RelativeGenusOneCubicFactorization

/-!
# The actual standard-chart preimages of the relative cubic map

The integral cubic factorization has the same generator opens as the original
projective presentation. Its Z chart is the marking complement, while its Y
chart contains the entire original marking over the varying base.
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

/-- Each integral chart pulls back to the actual original generator open. -/
theorem relativePointToIntegralCubic_preimage_chart (j : Fin 3) :
    relativePointToIntegralCubic G hg s hI e ⁻¹ᵁ (integralCurveChart (W) j).opensRange =
      sectionGeneratorOpen (tensorPower (L) 3) (T j) := by
  rw [← integralProjectiveMap_preimage_chart, ← Scheme.Hom.comp_preimage,
    relativePointToIntegralCubic_projective, relativePointToProjectiveSpace,
    sectionProjectiveMorphism_preimage_chart]

/-- The affine cubic chart has exactly the original marked-point complement as preimage. -/
theorem relativePointToIntegralCubic_preimage_z :
    relativePointToIntegralCubic G hg s hI e ⁻¹ᵁ (integralCurveChart (W) 2).opensRange =
      s.left.ker.support.compl := by
  rw [← integralProjectiveMap_preimage_chart, ← Scheme.Hom.comp_preimage,
    relativePointToIntegralCubic_projective, relativePointToProjectiveSpace_preimage_z]

/-- Along the original marking the Y generator open is the whole base. -/
theorem relativePointMarking_preimage_yGenerator :
    s.left ⁻¹ᵁ sectionGeneratorOpen (tensorPower (L) 3) (T 1) = ⊤ := by
  rw [← sectionPoleCoefficient_basicOpen s.left hI e 3,
    relativePointProjectiveSections_coefficient, Matrix.cons_val_one,
    Matrix.cons_val_zero, Scheme.basicOpen_one]

/-- The marking lands in the actual integral Y chart, including over nonreduced bases. -/
theorem relativePointMarking_preimage_y :
    (s.left ≫ relativePointToIntegralCubic G hg s hI e) ⁻¹ᵁ
      (integralCurveChart (W) 1).opensRange = ⊤ := by
  rw [Scheme.Hom.comp_preimage, relativePointToIntegralCubic_preimage_chart,
    relativePointMarking_preimage_yGenerator]

end FLT.Mazur.FCurve
