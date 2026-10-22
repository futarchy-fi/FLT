/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingHomogeneousEquation
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
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor tensorPower
  smoothMarkingProjectiveSections SectionGradedMultiplication.mul

variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingChartEquationProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)
local notation "T" => smoothMarkingProjectiveSections E s e
local notation "W" => smoothMarkingWeierstrassCurve E s e

/-- The regular normalized coordinates on a subopen of an original generator chart. -/
def smoothMarkingChartCoordinates (j : Fin 3) (U : E.curve.left.Opens)
    (hj : U ≤ sectionGeneratorOpen (tensorPower (L) 3) (T j)) : Fin 3 → Γ(E.curve.left, U) :=
  fun i => sectionRatioOn (tensorPower (L) 3) (T j) U hj (T i)

/-- The selected coordinate is exactly one. -/
theorem smoothMarkingChartCoordinates_self (j : Fin 3) (U : E.curve.left.Opens)
    (hj : U ≤ sectionGeneratorOpen (tensorPower (L) 3) (T j)) :
    smoothMarkingChartCoordinates E s e j U hj j = 1 :=
  sectionRatioOn_self _ _ _ _

/-- Every actual generator chart satisfies the normalized original cubic equation. -/
theorem smoothMarkingChartCoordinates_equation (j : Fin 3) (U : E.curve.left.Opens)
    (hj : U ≤ sectionGeneratorOpen (tensorPower (L) 3) (T j)) :
    ((W).map (sectionChartScalars E.curve.hom.appTop.hom U)).toProjective.Equation
      (smoothMarkingChartCoordinates E s e j U hj) := by
  rw [WeierstrassCurve.Projective.equation_iff, sub_eq_zero]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    pow_succ, pow_zero, one_mul]
  apply degreeThreeCubicProduct_smul_injective (L) (hI).divisorLineBundle_locallyFreeRankOne
    (T j) U hj
  have h := congrArg ((tensorPower (L) 9).presheaf.map U.leTop.op)
    (smoothMarkingProjectiveSections_equation E s e)
  simp only [map_add, (tensorPower (L) 9).map_smul] at h
  have hP : smoothMarkingCubicProduct E s = degreeThreeCubicProduct (L) ⊤ := by
    unfold smoothMarkingCubicProduct degreeThreeCubicProduct
    rfl
  have hp (a b c : Γ(tensorPower (L) 3, ⊤)) :
      (tensorPower (L) 9).presheaf.map U.leTop.op
        (smoothMarkingCubicProduct E s a b c) =
      (sectionRatioOn (tensorPower (L) 3) (T j) U hj a *
        sectionRatioOn (tensorPower (L) 3) (T j) U hj b *
        sectionRatioOn (tensorPower (L) 3) (T j) U hj c) •
      (tensorPower (L) 9).presheaf.map U.leTop.op
        (degreeThreeCubicProduct (L) ⊤ (T j) (T j) (T j)) := by
    rw [hP]
    exact (degreeThreeCubicProduct_ratios (L) (T j) a b c U hj).symm
  simp only [hp, smul_smul, ← add_smul] at h
  simp only [smoothMarkingChartCoordinates, smoothMarkingProjectiveSections,
    sectionChartScalars, RingHom.comp_apply, WeierstrassCurve.Projective.fin3_def_ext,
    mul_assoc] at h ⊢
  convert h using 1 <;> rfl

end FLT.Mazur.GeneralizedEllipticCurve
