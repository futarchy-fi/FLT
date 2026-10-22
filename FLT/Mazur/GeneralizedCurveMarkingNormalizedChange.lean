/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingNormalizedCoordinates
public import FLT.Mazur.GeneralizedCurveMarkingFrameEquation

/-!
# An admissible change from independently normalized original coordinates

The actual lower-pole corrections construct all four change parameters.
The horizontal correction is divided only by the known unit square, so the
construction retains arbitrary nilpotents and every residue characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory WeierstrassCurve
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates relativePoleFunction
  smoothMarkingWeierstrassCurve smoothMarkingChartRingEquiv
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)
local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)
variable (e f : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)
local notation "u" => smoothMarkingFrameUnit E s e f
local notation "φ" => smoothMarkingComplementBaseMap E s
local notation "W" => smoothMarkingWeierstrassCurve E s e
variable (x : ModuleRingH E.curve.hom.appTop.hom
    (tensorPower (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) 2) 0)
  (y : ModuleRingH E.curve.hom.appTop.hom
    (tensorPower (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) 3) 0)
  (hx : sectionPoleCoefficient (s ≫ E.inclusion).left
    (smoothMarking_relativeCartier E s).1 f 2 (moduleH0Equiv _ x) = 1)
  (hy : sectionPoleCoefficient (s ≫ E.inclusion).left
    (smoothMarking_relativeCartier E s).1 f 3 (moduleH0Equiv _ y) = 1)
local notation "fx" => relativePoleFunction E.curve.hom (Over.Hom.left (t)) (hI) 2 x
local notation "fy" => relativePoleFunction E.curve.hom (Over.Hom.left (t)) (hI) 3 y

include hx hy

/-- The actual normalized sections give the complete integral admissible-coordinate formula. -/
theorem smoothMarkingNormalizedCoordinates_change :
    ∃ C : VariableChange Γ(S, ⊤), C.u = u ∧
      fx = φ (C.u : Γ(S, ⊤)) ^ 2 * smoothMarkingComplementX E s e + φ C.r ∧
      fy = φ (C.u : Γ(S, ⊤)) ^ 3 * smoothMarkingComplementY E s e +
        φ (C.u : Γ(S, ⊤)) ^ 2 * φ C.s * smoothMarkingComplementX E s e + φ C.t := by
  obtain ⟨r, hr⟩ := smoothMarkingNormalizedX_correction E s e f x hx
  obtain ⟨b, c, hc⟩ := smoothMarkingNormalizedY_correction E s e f y hy
  refine ⟨⟨u, r, (Units.val ((u)⁻¹)) ^ 2 * b, c⟩, rfl, ?_, ?_⟩
  · simpa only [map_pow] using hr
  · have hb : φ (u : Γ(S, ⊤)) ^ 2 * φ ((Units.val ((u)⁻¹)) ^ 2 * b) = φ b := by
      rw [← map_pow, ← map_mul, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
    dsimp only
    rw [hc, map_pow, hb]
    ring

/-- Any equation satisfied by those original coordinates is the exact transformed equation. -/
theorem smoothMarkingNormalizedCoordinates_equation (V : WeierstrassCurve Γ(S, ⊤))
    (hV : (V.map (φ)).toAffine.Equation fx fy) :
    ∃ C : VariableChange Γ(S, ⊤), C.u = u ∧ C • V = W ∧
      fx = φ (C.u : Γ(S, ⊤)) ^ 2 * smoothMarkingComplementX E s e + φ C.r ∧
      fy = φ (C.u : Γ(S, ⊤)) ^ 3 * smoothMarkingComplementY E s e +
        φ (C.u : Γ(S, ⊤)) ^ 2 * φ C.s * smoothMarkingComplementX E s e + φ C.t := by
  obtain ⟨C, hu, hX, hY⟩ := smoothMarkingNormalizedCoordinates_change E s e f x y hx hy
  refine ⟨C, hu, ?_, hX, hY⟩
  apply affineEquation_curve_eq_of_injective (W) _ (φ)
    (smoothMarkingChartRingEquiv E s e).toRingHom
    (smoothMarkingChartRingEquiv E s e).injective
    (smoothMarkingChartRingEquiv_scalar E s e)
  change ((C • V).map (φ)).toAffine.Equation
    (smoothMarkingChartRingEquiv E s e (coord (W) 2 0))
    (smoothMarkingChartRingEquiv E s e (coord (W) 2 1))
  rw [smoothMarkingChartRingEquiv_x, smoothMarkingChartRingEquiv_y, ← map_variableChange]
  apply (WeierstrassVariableChangeIntegralEquation.equation_iff _ _ _ _).mp
  rw [hX, hY] at hV
  simpa only [VariableChange.map, Units.coe_map, MonoidHom.coe_ofClass] using hV

end FLT.Mazur.GeneralizedEllipticCurve
