/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFamilyEquation
public import FLT.Mazur.WeierstrassEvaluatedChangeUnique
public import FLT.Mazur.WeierstrassVariableChangeZero
public import FLT.Mazur.WeierstrassVariableChangeAffineRestriction

/-!
# The unique complete cubic comparison for an original family isomorphism

Actual complement functions determine all four coordinate parameters. The
resulting pointed cubic isomorphism retains the original coefficient base.
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

local notation "V" => smoothMarkingWeierstrassCurve F (s ≫ e.hom.group) b

/-- The actual transported coordinate functions determine a unique admissible change. -/
theorem smoothMarkingWeierstrass_familyIso_existsUnique :
    ∃! C : VariableChange Γ(S, ⊤), C.u = u ∧ C • W = V ∧
      (π).appTop (smoothMarkingComplementX E s a) =
        φ (C.u : Γ(S, ⊤)) ^ 2 * x + φ C.r ∧
      (π).appTop (smoothMarkingComplementY E s a) =
        φ (C.u : Γ(S, ⊤)) ^ 3 * y +
          φ (C.u : Γ(S, ⊤)) ^ 2 * φ C.s * x + φ C.t := by
  obtain ⟨C, hu, hC, hx, hy⟩ := smoothMarkingWeierstrass_familyIso_equation e s a b
  refine ⟨C, ⟨hu, hC, hx, hy⟩, ?_⟩
  rintro D ⟨_, hD, hDx, hDy⟩
  apply WeierstrassIntegralChart.evaluatedVariableChange_unique (V) (W)
    (φ) (smoothMarkingChartRingEquiv F (s ≫ e.hom.group) b).toRingHom
    (smoothMarkingChartRingEquiv F (s ≫ e.hom.group) b).injective
    (smoothMarkingChartRingEquiv_scalar F (s ≫ e.hom.group) b) D C hD hC
  · simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      smoothMarkingChartRingEquiv_x] using hDx.symm.trans hx
  · simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      smoothMarkingChartRingEquiv_x, smoothMarkingChartRingEquiv_y] using hDy.symm.trans hy

/-- The constructed full coordinate change for the specified original family isomorphism. -/
def smoothMarkingFamilyChange : VariableChange Γ(S, ⊤) :=
  (smoothMarkingWeierstrass_familyIso_existsUnique e s a b).exists.choose

/-- The chosen change retains the original frame unit, equation, and coordinate functions. -/
theorem smoothMarkingFamilyChange_spec :
    let C := smoothMarkingFamilyChange e s a b
    C.u = u ∧ C • W = V ∧
      (π).appTop (smoothMarkingComplementX E s a) =
        φ (C.u : Γ(S, ⊤)) ^ 2 * x + φ C.r ∧
      (π).appTop (smoothMarkingComplementY E s a) =
        φ (C.u : Γ(S, ⊤)) ^ 3 * y +
          φ (C.u : Γ(S, ⊤)) ^ 2 * φ C.s * x + φ C.t :=
  (smoothMarkingWeierstrass_familyIso_existsUnique e s a b).exists.choose_spec

open WeierstrassIntegralChart
attribute [local irreducible] smoothMarkingFamilyChange
local notation "C" => smoothMarkingFamilyChange e s a b
local notation "hC" => And.left (And.right (smoothMarkingFamilyChange_spec e s a b))

/-- The independently recomputed cubic is identified with the original complete cubic. -/
def smoothMarkingFamilyCubicIso : integralCurve (V) ≅ integralCurve (W) :=
  integralVariableChangeIso (W) (V) (C) (hC)

/-- The complete comparison retains its actual coefficient spectrum. -/
@[reassoc] theorem smoothMarkingFamilyCubicIso_over :
    (smoothMarkingFamilyCubicIso e s a b).hom ≫ integralCurveStructure (W) =
      integralCurveStructure (V) := integralVariableChangeTo_structure (W) (V) (C) (hC)

/-- The family comparison preserves the marking at infinity. -/
@[reassoc] theorem smoothMarkingFamilyCubicIso_zero :
    integralCurveZero (V) ≫ (smoothMarkingFamilyCubicIso e s a b).hom =
      integralCurveZero (W) := integralVariableChangeIso_zero (W) (V) (C) (hC)

/-- The complete comparison restricts to the same original coordinate substitution. -/
@[reassoc] theorem smoothMarkingFamilyCubicIso_affine :
    integralCurveChart (V) 2 ≫ (smoothMarkingFamilyCubicIso e s a b).hom =
      (affineVariableChangeIso (W) (V) (C) (hC)).hom ≫ integralCurveChart (W) 2 :=
  integralVariableChangeIso_affine (W) (V) (C) (hC)

end FLT.Mazur.GeneralizedEllipticCurve
