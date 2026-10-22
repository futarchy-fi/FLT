/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingBaseChangeCubic
public import FLT.Mazur.GeneralizedCurveMarkingFrameAffineChange
public import FLT.Mazur.WeierstrassChangedCoefficientEvaluation

/-!
# The original affine chart evaluation after arbitrary base change

The complete coordinate substitution and scalar coefficient map agree with
actual pullback of the original complement functions on the whole chart ring.
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

/-- Full chart evaluation commutes with actual pullback and the complete u,r,s,t change. -/
theorem smoothMarkingChartRingEquiv_baseChange :
    (Q').toRingHom.comp
      ((affineVariableChangeMap ((W).map g.appTop.hom) (V) (C) (hC)).toRingHom.comp
        (chartCoefficientRingMap g.appTop.hom (W) 2)) =
      (π).appTop.hom.comp (Q).toRingHom := by
  apply changedCoefficientEvaluation_eq g.appTop.hom (W) (V) (C) (hC)
    (smoothMarkingComplementBaseMap (E.baseChange g) (pullSection g s))
  · exact smoothMarkingChartRingEquiv_scalar (E.baseChange g) (pullSection g s) b
  · intro r
    change (π).appTop (Q (algebraMap Γ(S, ⊤) _ r)) = _
    rw [smoothMarkingChartRingEquiv_scalar]
    exact smoothMarkingComplementProjection_scalar E g s r
  · simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, smoothMarkingChartRingEquiv_x] using
      (smoothMarkingBaseChangeChange_spec E g s a b).2.2.1.symm
  · simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, smoothMarkingChartRingEquiv_x,
      smoothMarkingChartRingEquiv_y] using
      (smoothMarkingBaseChangeChange_spec E g s a b).2.2.2.symm

end FLT.Mazur.GeneralizedEllipticCurve
