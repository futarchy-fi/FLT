/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingBaseChangeEvaluation
public import FLT.Mazur.WeierstrassAffineEvaluationNaturality

/-!
# Naturality of the actual affine cubic morphism

The coordinate-ring comparison gives the commuting square of actual complement
morphisms, with both the full variable change and coefficient map retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory WeierstrassCurve
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates relativePoleFunction
  smoothMarkingWeierstrassCurve smoothMarkingChartRingEquiv smoothMarkingTransportedLift
  smoothMarkingTransportedFrame affineVariableChangeMap smoothMarkingBaseChangeChange
  chartCoefficientRingMap smoothMarkingComplementProjection smoothMarkingComplementBaseMap
variable {S T : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
  (E : GeneralizedEllipticCurve S) (g : T ⟶ S) (s : 𝟙_ (Over S) ⟶ E.group)
  (a : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)
  (b : (pullback (pullSection g s ≫ (E.baseChange g).inclusion).left).obj
    (divisorLineBundle (pullSection g s ≫ (E.baseChange g).inclusion).left.ker
      (smoothMarking_relativeCartier (E.baseChange g) (pullSection g s)).1) ≅ structureModule T)
local notation "W" => smoothMarkingWeierstrassCurve E s a
local notation "V" => smoothMarkingWeierstrassCurve (E.baseChange g) (pullSection g s) b
local notation "C" => smoothMarkingBaseChangeChange E g s a b
local notation "hC" => And.left (And.right (smoothMarkingBaseChangeChange_spec E g s a b))
local notation "π" => smoothMarkingComplementProjection E g s
local notation "Q" => smoothMarkingChartRingEquiv E s a
local notation "Q'" => smoothMarkingChartRingEquiv (E.baseChange g) (pullSection g s) b

/-- The actual affine morphism commutes with arbitrary base change and all four parameters. -/
theorem smoothMarkingToIntegralAffineChart_baseChange :
    smoothMarkingToIntegralAffineChart (E.baseChange g) (pullSection g s) b ≫
      (affineVariableChangeIso ((W).map g.appTop.hom) (V) (C) (hC)).hom ≫
        Spec.map (CommRingCat.ofHom (chartCoefficientRingMap g.appTop.hom (W) 2)) =
      (π) ≫ smoothMarkingToIntegralAffineChart E s a := by
  exact affineEvaluation_coefficient_square (π) g.appTop.hom (W) (V) (C) (hC)
    (Q').toRingHom (Q).toRingHom (smoothMarkingChartRingEquiv_baseChange E g s a b)

end FLT.Mazur.GeneralizedEllipticCurve
