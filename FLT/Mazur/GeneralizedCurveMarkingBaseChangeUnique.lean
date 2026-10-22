/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingBaseChangeEquation
public import FLT.Mazur.WeierstrassEvaluatedChangeUnique

/-!
# The unique actual base-change coordinate transformation

The equality of original complement functions determines the complete
admissible change. This makes the comparison independent of proof choices
and retains the transition unit from the actual transported marked line.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory WeierstrassCurve
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange ModuleLineBundleTensorPullback
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

/-- The original coordinate functions determine exactly one full base-change transformation. -/
theorem smoothMarkingWeierstrass_baseChange_existsUnique :
    ∃! C : VariableChange Γ(T, ⊤), C.u = u ∧ C • (W).map g.appTop.hom = V ∧
      (π).appTop (smoothMarkingComplementX E s a) =
        φ (C.u : Γ(T, ⊤)) ^ 2 * x + φ C.r ∧
      (π).appTop (smoothMarkingComplementY E s a) =
        φ (C.u : Γ(T, ⊤)) ^ 3 * y +
          φ (C.u : Γ(T, ⊤)) ^ 2 * φ C.s * x + φ C.t := by
  obtain ⟨C, hu, hC, hx, hy⟩ := smoothMarkingWeierstrass_baseChange_equation E g s a b
  refine ⟨C, ⟨hu, hC, hx, hy⟩, ?_⟩
  rintro D ⟨_, hD, hDx, hDy⟩
  apply WeierstrassIntegralChart.evaluatedVariableChange_unique (V) ((W).map g.appTop.hom)
    (φ) (smoothMarkingChartRingEquiv (E.baseChange g) (pullSection g s) b).toRingHom
    (smoothMarkingChartRingEquiv (E.baseChange g) (pullSection g s) b).injective
    (smoothMarkingChartRingEquiv_scalar (E.baseChange g) (pullSection g s) b) D C hD hC
  · simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      smoothMarkingChartRingEquiv_x] using hDx.symm.trans hx
  · simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      smoothMarkingChartRingEquiv_x, smoothMarkingChartRingEquiv_y] using hDy.symm.trans hy

end FLT.Mazur.GeneralizedEllipticCurve
