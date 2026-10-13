/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalInfinityShear
public import FLT.Mazur.WeierstrassSplitNormalizationInfinityParameter
public import FLT.Mazur.NodeTangentSplitNormalizationComparison
public import FLT.Mazur.WeierstrassRootShearSmoothParameter

/-!
# The nonsplit normalization retains the whole original infinity chart

First apply inverse root shear on the entire original chart, then the proved
split infinity parameter. The complete original cubic and coefficient maps survive.
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

/-- The complete original infinity chart maps to the root-sheared normalization parameter. -/
def nodeTangentInfinityParameter : chartScheme U 1 ⟶ scheme Q :=
  nodalInfinityShear U h3 h4 h6 r hr ≫ splitEquationInfinityParameter V a he

/-- Its coefficient map is the actual root-extension field, on the entire source chart. -/
@[reassoc] theorem nodeTangentInfinityParameter_structure :
    nodeTangentInfinityParameter W h₃ h₄ h₆ a ha ≫ toBase Q = chartStructure U 1 := by
  rw [nodeTangentInfinityParameter, Category.assoc,
    splitEquationInfinityParameter_structure]
  exact nodalInfinityShear_structure U h3 h4 h6 r hr

/-- The parameter reconstructs the original coefficient-extended cubic chart after root shear. -/
@[reassoc] theorem nodeTangentInfinityParameter_split :
    nodeTangentInfinityParameter W h₃ h₄ h₆ a ha ≫
      splitCompleteNormalization V (b).1 (b).2.1 (b).2.2.1 (b).2.2.2 ≫
        (integralVariableChangeIso U V (WeierstrassCurve.VariableChange.mk 1 0 r 0) rfl).hom =
      integralCurveChart U 1 := by
  rw [nodeTangentInfinityParameter, Category.assoc,
    splitEquationInfinityParameter_normalization_assoc]
  exact nodalInfinityShear_reconstruction U h3 h4 h6 r hr

/-- The complete nonsplit normalization retains the full original infinity coefficient map. -/
@[reassoc] theorem nodeTangentInfinityParameter_normalization :
    nodeTangentInfinityParameter W h₃ h₄ h₆ a ha ≫
      nodeTangentCompleteNormalization W h₃ h₄ h₆ =
        chartCoefficientMorphism W 1 ≫ integralCurveChart W 1 := by
  rw [nodeTangentCompleteNormalization_eq_split,
    nodeTangentInfinityParameter_split_assoc, integralCurveChart_coefficientMorphism]

end FLT.Mazur
