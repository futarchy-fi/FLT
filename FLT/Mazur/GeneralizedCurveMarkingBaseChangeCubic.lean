/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingBaseChangeUnique
public import FLT.Mazur.WeierstrassVariableChangeZero
public import FLT.Mazur.WeierstrassVariableChangeAffineRestriction

/-!
# The complete pointed cubic comparison after actual base change

The uniquely determined coordinate transformation gives an isomorphism
from the independently recomputed cubic to the scalar pullback of the
original equation. Its base, infinity section, and affine substitution
are retained explicitly.
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
  smoothMarkingTransportedFrame
variable {S T : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
  (E : GeneralizedEllipticCurve S) (g : T ⟶ S) (s : 𝟙_ (Over S) ⟶ E.group)
  (a : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)
  (b : (pullback (pullSection g s ≫ (E.baseChange g).inclusion).left).obj
    (divisorLineBundle (pullSection g s ≫ (E.baseChange g).inclusion).left.ker
      (smoothMarking_relativeCartier (E.baseChange g) (pullSection g s)).1) ≅ structureModule T)
local notation "v" => pullSection g s ≫ GeneralizedEllipticCurve.inclusion (E.baseChange g)
local notation "hJ" => And.left (smoothMarking_relativeCartier (E.baseChange g) (pullSection g s))
local notation "φ" => smoothMarkingComplementBaseMap (E.baseChange g) (pullSection g s)
local notation "x" => smoothMarkingComplementX (E.baseChange g) (pullSection g s) b
local notation "y" => smoothMarkingComplementY (E.baseChange g) (pullSection g s) b
local notation "fx" => relativePoleFunction
  (Over.hom (GeneralizedEllipticCurve.curve (E.baseChange g))) (Over.Hom.left (v)) (hJ) 2
  (smoothMarkingTransportedLift E g s a 1 (by decide))
local notation "fy" => relativePoleFunction
  (Over.hom (GeneralizedEllipticCurve.curve (E.baseChange g))) (Over.Hom.left (v)) (hJ) 3
  (smoothMarkingTransportedLift E g s a 2 (by decide))
local notation "u" => frameComparisonUnit b (smoothMarkingTransportedFrame E g s a) ⊤

local notation "π" => smoothMarkingComplementProjection E g s
local notation "W" => smoothMarkingWeierstrassCurve E s a

local notation "V" => smoothMarkingWeierstrassCurve (E.baseChange g) (pullSection g s) b

/-- The unique full change constructed from the actual transported coordinate sections. -/
def smoothMarkingBaseChangeChange : VariableChange Γ(T, ⊤) :=
  (smoothMarkingWeierstrass_baseChange_existsUnique E g s a b).exists.choose

/-- All four parameters retain their actual original complement-coordinate formulas. -/
theorem smoothMarkingBaseChangeChange_spec :
    let C := smoothMarkingBaseChangeChange E g s a b
    C.u = u ∧ C • (W).map g.appTop.hom = V ∧
      (π).appTop (smoothMarkingComplementX E s a) =
        φ (C.u : Γ(T, ⊤)) ^ 2 * x + φ C.r ∧
      (π).appTop (smoothMarkingComplementY E s a) =
        φ (C.u : Γ(T, ⊤)) ^ 3 * y +
          φ (C.u : Γ(T, ⊤)) ^ 2 * φ C.s * x + φ C.t :=
  (smoothMarkingWeierstrass_baseChange_existsUnique E g s a b).exists.choose_spec

attribute [local irreducible] smoothMarkingBaseChangeChange
local notation "C" => smoothMarkingBaseChangeChange E g s a b
local notation "hC" => And.left (And.right (smoothMarkingBaseChangeChange_spec E g s a b))

/-- The complete cubic of the changed family is isomorphic to the pulled original equation. -/
def smoothMarkingBaseChangeCubicIso :
    integralCurve (V) ≅ integralCurve ((W).map g.appTop.hom) :=
  integralVariableChangeIso ((W).map g.appTop.hom) (V) (C) (hC)

/-- The complete comparison retains the changed base spectrum. -/
@[reassoc] theorem smoothMarkingBaseChangeCubicIso_over :
    (smoothMarkingBaseChangeCubicIso E g s a b).hom ≫
      integralCurveStructure ((W).map g.appTop.hom) = integralCurveStructure (V) :=
  integralVariableChangeTo_structure ((W).map g.appTop.hom) (V) (C) (hC)

/-- The comparison preserves the original pointed cubic's infinity section. -/
@[reassoc] theorem smoothMarkingBaseChangeCubicIso_zero :
    integralCurveZero (V) ≫ (smoothMarkingBaseChangeCubicIso E g s a b).hom =
      integralCurveZero ((W).map g.appTop.hom) :=
  integralVariableChangeIso_zero ((W).map g.appTop.hom) (V) (C) (hC)

/-- The full comparison restricts to the same explicit affine coordinate substitution. -/
@[reassoc] theorem smoothMarkingBaseChangeCubicIso_affine :
    integralCurveChart (V) 2 ≫ (smoothMarkingBaseChangeCubicIso E g s a b).hom =
      (affineVariableChangeIso ((W).map g.appTop.hom) (V) (C) (hC)).hom ≫
        integralCurveChart ((W).map g.appTop.hom) 2 :=
  integralVariableChangeIso_affine ((W).map g.appTop.hom) (V) (C) (hC)

end FLT.Mazur.GeneralizedEllipticCurve
