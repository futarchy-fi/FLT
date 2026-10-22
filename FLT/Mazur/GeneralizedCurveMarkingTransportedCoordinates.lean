/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingTransportedFrame
public import FLT.Mazur.GeneralizedCurveMarkingNormalizedChange

/-!
# Full coordinate corrections on the actual changed curve

The transported original sections and the independently constructed new
coordinates have an integral admissible change. All four parameters are
constructed from the new family's lower-pole bases; their existence is
not supplied as a compatibility hypothesis.
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

/-- Actual transported sections have all four coordinate-change parameters on the new family. -/
theorem smoothMarkingTransportedCoordinates_change :
    ∃ C : VariableChange Γ(T, ⊤), C.u = u ∧
      fx = φ (C.u : Γ(T, ⊤)) ^ 2 * x + φ C.r ∧
      fy = φ (C.u : Γ(T, ⊤)) ^ 3 * y +
        φ (C.u : Γ(T, ⊤)) ^ 2 * φ C.s * x + φ C.t := by
  exact smoothMarkingNormalizedCoordinates_change (E.baseChange g) (pullSection g s)
    b (smoothMarkingTransportedFrame E g s a) _ _
    (smoothMarkingTransportedLift_coefficient E g s a 1 (by decide))
    (smoothMarkingTransportedLift_coefficient E g s a 2 (by decide))

/-- Any equation of the transported sections is identified by this same full coordinate change. -/
theorem smoothMarkingTransportedCoordinates_equation (V : WeierstrassCurve Γ(T, ⊤))
    (hV : (V.map (φ)).toAffine.Equation fx fy) :
    ∃ C : VariableChange Γ(T, ⊤), C.u = u ∧
      C • V = smoothMarkingWeierstrassCurve (E.baseChange g) (pullSection g s) b ∧
      fx = φ (C.u : Γ(T, ⊤)) ^ 2 * x + φ C.r ∧
      fy = φ (C.u : Γ(T, ⊤)) ^ 3 * y +
        φ (C.u : Γ(T, ⊤)) ^ 2 * φ C.s * x + φ C.t := by
  exact smoothMarkingNormalizedCoordinates_equation (E.baseChange g) (pullSection g s)
    b (smoothMarkingTransportedFrame E g s a) _ _
    (smoothMarkingTransportedLift_coefficient E g s a 1 (by decide))
    (smoothMarkingTransportedLift_coefficient E g s a 2 (by decide)) V hV

end FLT.Mazur.GeneralizedEllipticCurve
