/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFamilyComplement
public import FLT.Mazur.GeneralizedCurveMarkingNormalizedChange

/-!
# Recomputed cubic equations across an original family isomorphism

The transported original pole sections satisfy the original equation. Their
normalization constructs the full admissible change to an independent frame
on the identified family, including all lower-pole corrections.
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

/-- Transported sections satisfy the actual original equation on the identified family. -/
theorem smoothMarkingFamilyLift_equation : ((W).map (φ)).toAffine.Equation fx fy := by
  have hh := (smoothMarkingWeierstrass_equation E s a).map (π).appTop.hom
  have hr : (π).appTop.hom.comp (smoothMarkingComplementBaseMap E s) = φ := by
    ext r
    exact smoothMarkingFamilyComplementMap_scalar e s r
  change (((W).map (smoothMarkingComplementBaseMap E s)).map (π).appTop.hom).toAffine.Equation
    ((π).appTop (smoothMarkingComplementX E s a))
    ((π).appTop (smoothMarkingComplementY E s a)) at hh
  rw [WeierstrassCurve.map_map, hr] at hh
  rw [smoothMarkingComplementX, smoothMarkingComplementY,
    smoothMarkingFamilyComplementMap_lift, smoothMarkingFamilyComplementMap_lift] at hh
  exact hh

/-- Independent frames on isomorphic original families have a full constructed u,r,s,t change. -/
theorem smoothMarkingWeierstrass_familyIso_equation :
    ∃ C : VariableChange Γ(S, ⊤), C.u = u ∧
      C • W = smoothMarkingWeierstrassCurve F (s ≫ e.hom.group) b ∧
      (π).appTop (smoothMarkingComplementX E s a) =
        φ (C.u : Γ(S, ⊤)) ^ 2 * x + φ C.r ∧
      (π).appTop (smoothMarkingComplementY E s a) =
        φ (C.u : Γ(S, ⊤)) ^ 3 * y +
          φ (C.u : Γ(S, ⊤)) ^ 2 * φ C.s * x + φ C.t := by
  have hh := smoothMarkingNormalizedCoordinates_equation F (s ≫ e.hom.group)
    b (smoothMarkingFamilyFrame e s a) _ _
    (smoothMarkingFamilyLift_coefficient e s a 1 (by decide))
    (smoothMarkingFamilyLift_coefficient e s a 2 (by decide)) (W)
    (smoothMarkingFamilyLift_equation e s a)
  simpa only [smoothMarkingComplementX, smoothMarkingComplementY,
    smoothMarkingFamilyComplementMap_lift, smoothMarkingFrameUnit] using hh

end FLT.Mazur.GeneralizedEllipticCurve
