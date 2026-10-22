/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingTransportedCoordinates
public import FLT.Mazur.GeneralizedCurveMarkingComplementPullback

/-!
# The recomputed relative cubic under actual base change

The transported coordinates satisfy the scalar pullback of the original
Weierstrass equation. Their full admissible change therefore identifies
that equation with the independently recomputed new-family equation.
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

omit [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] in
/-- The actual transported sections satisfy the scalar pullback of the original equation. -/
theorem smoothMarkingTransportedCoordinates_originalEquation :
    (((W).map g.appTop.hom).map (φ)).toAffine.Equation fx fy := by
  have hh := (smoothMarkingWeierstrass_equation E s a).map (π).appTop.hom
  have hr : (π).appTop.hom.comp (smoothMarkingComplementBaseMap E s) =
      (φ).comp g.appTop.hom := by
    ext r
    exact smoothMarkingComplementProjection_scalar E g s r
  change (((W).map (smoothMarkingComplementBaseMap E s)).map (π).appTop.hom).toAffine.Equation
    ((π).appTop (smoothMarkingComplementX E s a))
    ((π).appTop (smoothMarkingComplementY E s a)) at hh
  rw [WeierstrassCurve.map_map, hr, smoothMarkingComplementProjection_x,
    smoothMarkingComplementProjection_y] at hh
  simpa only [WeierstrassCurve.map_map] using hh

/-- The original and independently recomputed equations have the actual full u,r,s,t change. -/
theorem smoothMarkingWeierstrass_baseChange_equation :
    ∃ C : VariableChange Γ(T, ⊤), C.u = u ∧
      C • (W).map g.appTop.hom =
        smoothMarkingWeierstrassCurve (E.baseChange g) (pullSection g s) b ∧
      (π).appTop (smoothMarkingComplementX E s a) =
        φ (C.u : Γ(T, ⊤)) ^ 2 * x + φ C.r ∧
      (π).appTop (smoothMarkingComplementY E s a) =
        φ (C.u : Γ(T, ⊤)) ^ 3 * y +
          φ (C.u : Γ(T, ⊤)) ^ 2 * φ C.s * x + φ C.t := by
  have hh := smoothMarkingTransportedCoordinates_equation E g s a b
    ((W).map g.appTop.hom) (smoothMarkingTransportedCoordinates_originalEquation E g s a)
  rw [smoothMarkingComplementProjection_x, smoothMarkingComplementProjection_y]
  exact hh

end FLT.Mazur.GeneralizedEllipticCurve
