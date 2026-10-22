/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFamilyCubic
public import FLT.Mazur.GeneralizedCurveMarkingFrameAffineChange
public import FLT.Mazur.WeierstrassChangedEvaluationSquare

/-!
# The actual affine cubic map under an original family isomorphism

The full coordinate substitution agrees with pullback on the original marking
complement. Passing to spectra retains the actual affine cubic morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory WeierstrassCurve
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates relativePoleFunction
  smoothMarkingWeierstrassCurve smoothMarkingChartRingEquiv smoothMarkingFamilyLift
  smoothMarkingFamilyFrame
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  {E F : GeneralizedEllipticCurve S} (e : E ≅ F) (s : 𝟙_ (Over S) ⟶ E.group)
  (a : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)
  (b : (pullback ((s ≫ e.hom.group) ≫ F.inclusion).left).obj
    (divisorLineBundle ((s ≫ e.hom.group) ≫ F.inclusion).left.ker
      (smoothMarking_relativeCartier F (s ≫ e.hom.group)).1) ≅ structureModule S)
local notation "v" => (s ≫ e.hom.group) ≫ F.inclusion
local notation "hJ" => And.left (smoothMarking_relativeCartier F (s ≫ e.hom.group))
local notation "φ" => smoothMarkingComplementBaseMap F (s ≫ e.hom.group)
local notation "x" => smoothMarkingComplementX F (s ≫ e.hom.group) b
local notation "y" => smoothMarkingComplementY F (s ≫ e.hom.group) b
local notation "fx" => relativePoleFunction F.curve.hom (Over.Hom.left (v)) (hJ) 2
  (smoothMarkingFamilyLift e s a 1 (by decide))
local notation "fy" => relativePoleFunction F.curve.hom (Over.Hom.left (v)) (hJ) 3
  (smoothMarkingFamilyLift e s a 2 (by decide))
local notation "π" => smoothMarkingFamilyComplementMap e s
local notation "W" => smoothMarkingWeierstrassCurve E s a
local notation "u" => frameComparisonUnit b (smoothMarkingFamilyFrame e s a) ⊤

open WeierstrassIntegralChart
attribute [local irreducible] affineVariableChangeMap smoothMarkingFamilyChange
  smoothMarkingFamilyComplementMap smoothMarkingComplementBaseMap
local notation "V" => smoothMarkingWeierstrassCurve F (s ≫ e.hom.group) b
local notation "C" => smoothMarkingFamilyChange e s a b
local notation "hC" => And.left (And.right (smoothMarkingFamilyChange_spec e s a b))
local notation "Q" => smoothMarkingChartRingEquiv E s a
local notation "Q'" => smoothMarkingChartRingEquiv F (s ≫ e.hom.group) b

/-- Full evaluation agrees with pullback along the actual identified-family complement map. -/
theorem smoothMarkingChartRingEquiv_familyIso :
    (Q').toRingHom.comp (affineVariableChangeMap (W) (V) (C) (hC)).toRingHom =
      (π).appTop.hom.comp (Q).toRingHom := by
  apply changedEvaluation_eq (W) (V) (C) (hC) (φ)
  · exact smoothMarkingChartRingEquiv_scalar F (s ≫ e.hom.group) b
  · intro r
    change (π).appTop (Q (algebraMap Γ(S, ⊤) _ r)) = _
    rw [smoothMarkingChartRingEquiv_scalar]
    exact smoothMarkingFamilyComplementMap_scalar e s r
  · simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, smoothMarkingChartRingEquiv_x] using
      (smoothMarkingFamilyChange_spec e s a b).2.2.1.symm
  · simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, smoothMarkingChartRingEquiv_x,
      smoothMarkingChartRingEquiv_y] using (smoothMarkingFamilyChange_spec e s a b).2.2.2.symm

/-- The independently constructed affine maps commute with the actual family identification. -/
theorem smoothMarkingToIntegralAffineChart_familyIso :
    smoothMarkingToIntegralAffineChart F (s ≫ e.hom.group) b ≫
      (affineVariableChangeIso (W) (V) (C) (hC)).hom =
        (π) ≫ smoothMarkingToIntegralAffineChart E s a := by
  exact affineEvaluation_variable_square (π) (W) (V) (C) (hC) (Q').toRingHom (Q).toRingHom
    (smoothMarkingChartRingEquiv_familyIso e s a b)

end FLT.Mazur.GeneralizedEllipticCurve
