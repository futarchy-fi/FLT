/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitInfinitySlopeCompatibility
public import FLT.Mazur.NodeTangentNormalizationInfinity
import all FLT.Mazur.NodeTangentNormalizationInfinity
public import FLT.Mazur.WeierstrassSplitNormalizationInfinityParameter
public import FLT.Mazur.NodeTangentSplitNormalizationComparison
public import FLT.Mazur.WeierstrassRootShearSmoothParameter

/-!
# The original nonsplit infinity parameter retains the full punctured slope

Compare the actual cubic maps before canceling the inverse root shear.
The source may be any scheme mapping to the complete punctured slope line.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur
open WeierstrassIntegralChart WeierstrassDividedDepth ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {F : Type} [Field F] (W : WeierstrassCurve F)
  [Fact (Irreducible (nodeTangentPolynomial W))]
  (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial W)
local notation "U" => W.map (algebraMap F Q)
local notation "V" => nodeTangentShear W
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "h3" => show (U).a₃ = 0 from by simp only [WeierstrassCurve.map_a₃, h₃, map_zero]
local notation "h4" => show (U).a₄ = 0 from by simp only [WeierstrassCurve.map_a₄, h₄, map_zero]
local notation "h6" => show (U).a₆ = 0 from by simp only [WeierstrassCurve.map_a₆, h₆, map_zero]
local notation "hr" => nodeTangentRoot_equation W
variable (a : (AdjoinRoot (nodeTangentPolynomial W))ˣ)
  (ha : (a : AdjoinRoot (nodeTangentPolynomial W)) = (nodeTangentShear W).a₁)
local notation "he" => rootShearCurve_eq_splitNodal U r a
  (ha.trans (nodeTangentShear_coefficients W).1) hr h3 h4 h6
local notation "b" => nodeTangentShear_normalization_coefficients W h₃ h₄ h₆

local notation "i" => integralVariableChangeIso U V
  (WeierstrassCurve.VariableChange.mk 1 0 r 0) rfl
local notation "s" => PrincipalOpenTransport.inclusion
  (WeierstrassModificationX.slopePolynomial (a : Q))
local notation "N" => splitCompleteNormalization V (b).1 (b).2.1 (b).2.2.1 (b).2.2.2

/-- The full original infinity parameter agrees with its punctured slope reconstruction. -/
theorem nodeTangentInfinityParameter_slope {X : Scheme}
    (f : X ⟶ Spec (.of (WeierstrassModificationX.SlopeOpen (a : Q))))
    (g : X ⟶ chartScheme U 1)
    (h : g ≫ integralCurveChart U 1 = f ≫ s ≫ left Q ≫ N ≫ (i).hom) :
    g ≫ nodeTangentInfinityParameter W h₃ h₄ h₆ a ha = f ≫ s ≫ left Q := by
  rw [nodeTangentInfinityParameter, ← Category.assoc]
  apply splitEquationInfinityParameter_slope V a he
    (b).1 (b).2.1 (b).2.2.1 (b).2.2.2
  apply (cancel_mono (i).hom).mp
  simp only [Category.assoc]
  erw [nodalInfinityShear_reconstruction U h3 h4 h6 r hr]
  rw [h, ← splitCompleteNormalization_left V (b).1 (b).2.1 (b).2.2.1 (b).2.2.2]
  simp only [Category.assoc]

end FLT.Mazur
