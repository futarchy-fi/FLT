/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeGenusOneHomogeneousEquation
public import FLT.Mazur.SectionCubicRatioNormalization
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

/-!
# The original cubic equation on every generator chart

Dividing the global homogeneous relation by the cube of the chosen generator
gives the actual normalized Weierstrass equation. This includes the chart
through the marking and does not require a reduced or field base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (G : Over S) [GrpObj G] [IsProper G.hom]
  [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  (hg : CurveFiberHypotheses.NodalGenusOneGeometricFibers G.hom)
  (s : 𝟙_ (Over S) ⟶ G) (hI : EffectiveCartier s.left.ker)
  (e : (pullback s.left).obj (divisorLineBundle s.left.ker hI) ≅ structureModule S)

local notation "L" => divisorLineBundle s.left.ker hI
local notation "T" => relativePointProjectiveSections G hg s hI e
local notation "W" => relativePointWeierstrassCurve G hg s hI e

/-- The regular normalized coordinates on a subopen of an original generator chart. -/
def relativePointChartCoordinates (j : Fin 3) (U : G.left.Opens)
    (hj : U ≤ sectionGeneratorOpen (tensorPower (L) 3) (T j)) : Fin 3 → Γ(G.left, U) :=
  fun i => sectionRatioOn (tensorPower (L) 3) (T j) U hj (T i)

/-- The selected coordinate is exactly one. -/
theorem relativePointChartCoordinates_self (j : Fin 3) (U : G.left.Opens)
    (hj : U ≤ sectionGeneratorOpen (tensorPower (L) 3) (T j)) :
    relativePointChartCoordinates G hg s hI e j U hj j = 1 :=
  sectionRatioOn_self _ _ _ _

/-- Every actual generator chart satisfies the normalized original cubic equation. -/
theorem relativePointChartCoordinates_equation (j : Fin 3) (U : G.left.Opens)
    (hj : U ≤ sectionGeneratorOpen (tensorPower (L) 3) (T j)) :
    ((W).map (sectionChartScalars G.hom.appTop.hom U)).toProjective.Equation
      (relativePointChartCoordinates G hg s hI e j U hj) := by
  rw [WeierstrassCurve.Projective.equation_iff, sub_eq_zero]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    pow_succ, pow_zero, one_mul]
  apply degreeThreeCubicProduct_smul_injective (L) hI.divisorLineBundle_locallyFreeRankOne
    (T j) U hj
  have h := congrArg ((tensorPower (L) 9).presheaf.map U.leTop.op)
    (relativePointProjectiveSections_equation G hg s hI e)
  simp only [map_add, (tensorPower (L) 9).map_smul] at h
  have hp (a b c : Γ(tensorPower (L) 3, ⊤)) :
      (tensorPower (L) 9).presheaf.map U.leTop.op
        (relativePointCubicProduct G s hI a b c) =
      (sectionRatioOn (tensorPower (L) 3) (T j) U hj a *
        sectionRatioOn (tensorPower (L) 3) (T j) U hj b *
        sectionRatioOn (tensorPower (L) 3) (T j) U hj c) •
      (tensorPower (L) 9).presheaf.map U.leTop.op
        (degreeThreeCubicProduct (L) ⊤ (T j) (T j) (T j)) :=
    (degreeThreeCubicProduct_ratios (L) (T j) a b c U hj).symm
  simp only [hp, smul_smul, ← add_smul] at h
  simp only [relativePointChartCoordinates, relativePointProjectiveSections,
    sectionChartScalars, RingHom.comp_apply, WeierstrassCurve.Projective.fin3_def_ext,
    mul_assoc] at h ⊢
  convert h using 1 <;> rfl

end FLT.Mazur.FCurve
